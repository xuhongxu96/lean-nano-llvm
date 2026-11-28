import Std.Data.HashMap
import LeanNanoLlvm.Semantics.Module
import LeanNanoLlvm.Llubi.AsmWriter
import LeanNanoLlvm.Llubi.IntrinsicAttrs

/-!
# `llubi`-compatible frontend

`lean-nano-llvm llubi [options] [file.ll | -] [program args...]` runs a module with the verified
small-step semantics (`execStep`) and reproduces the observable behaviour of LLVM's `llubi`:

* the same command-line options (`--verbose`, `--entry-function`, `--max-mem`, `--max-steps`,
  `--max-stack-depth`, `--vscale`, `--seed`, `--deterministic`, `--fuse-fmuladd`,
  `--disable-verify`, `--undef-behavior`, `--nan-behavior`),
* the same `--verbose` trace on stderr (`Entering function:`, `  <instr> => <value>`,
  `  <terminator> jump to %bb`, `Exiting function:`), program output (`printf`, `puts`, ...) on
  stdout, the `Stacktrace:` / `Immediate UB detected:` / `Error:` diagnostics, and
* the same process exit code.

This lets LLVM's own `llvm/test/tools/llubi` suite run unmodified under `lit` + `FileCheck`
with `llubi` substituted by this frontend.
-/

namespace LeanNanoLlvm.Llubi

open LeanNanoLlvm.AST
open LeanNanoLlvm.AST.Parser
open LeanNanoLlvm.Semantics

/-! ### Options -/

structure Options where
  file          : String := "-"
  progArgs      : List String := []
  entry         : String := "main"
  fakeArgv0     : String := ""
  verbose       : Bool := false
  maxMem        : Nat := 4294967295
  maxSteps      : Nat := 0
  maxStackDepth : Nat := 256
  vscale        : Nat := 4
  seed          : Nat := 0
  deterministic : Bool := false
  fuseFMulAdd   : Bool := true
  noVerify      : Bool := false
  undefMode?    : Option String := none
  nanMode       : String := "nondet"
deriving Inhabited

private def boolOpt (v : String) : Except String Bool :=
  match v.toLower with
  | "true" | "1" | "" => .ok true
  | "false" | "0" => .ok false
  | _ => .error s!"invalid boolean value '{v}'"

private def natOpt (name v : String) : Except String Nat :=
  match v.toNat? with
  | some n => .ok n
  | none => .error s!"for the --{name} option: '{v}' value invalid for uint argument!"

/-- Setter of an option that takes a value (`--opt=v` or `--opt v`), if `name` is one. -/
private def valueOpt (name : String) : Option (String → Options → Except String Options) :=
  match name with
  | "entry-function" => some fun v o => .ok { o with entry := v }
  | "fake-argv0" => some fun v o => .ok { o with fakeArgv0 := v }
  | "max-mem" => some fun v o => do let n ← natOpt name v; .ok { o with maxMem := n }
  | "max-steps" => some fun v o => do let n ← natOpt name v; .ok { o with maxSteps := n }
  | "max-stack-depth" => some fun v o => do let n ← natOpt name v; .ok { o with maxStackDepth := n }
  | "vscale" => some fun v o => do let n ← natOpt name v; .ok { o with vscale := n }
  | "seed" => some fun v o => do let n ← natOpt name v; .ok { o with seed := n }
  | "undef-behavior" => some fun v o =>
    if v == "nondet" || v == "zero" then .ok { o with undefMode? := some v }
    else .error s!"for the --undef-behavior option: Cannot find option named '{v}'!"
  | "nan-behavior" => some fun v o =>
    if ["nondet", "preferred", "quieting", "unchanged", "target-specific"].contains v then
      .ok { o with nanMode := v }
    else .error s!"for the --nan-behavior option: Cannot find option named '{v}'!"
  | _ => none

/-- Parse `llubi` command-line options (LLVM `cl::opt` syntax: `-opt`, `--opt`, `--opt=v`, `--opt v`). -/
def parseOptions (args : List String) : Except String Options :=
  go {} false args
where
  go (o : Options) (seenFile : Bool) : List String → Except String Options
    | [] => .ok o
    | a :: rest =>
      if seenFile then .ok { o with progArgs := o.progArgs ++ (a :: rest) }
      else if a == "-" then go { o with file := "-" } true rest
      else if a.startsWith "-" then
        let body := (a.dropWhile (· == '-')).toString
        let (name, val?) := match body.splitOn "=" with
          | [n] => (n, none)
          | n :: vs => (n, some ("=".intercalate vs))
          | [] => (body, none)
        match name with
        | "verbose" => do let b ← boolOpt (val?.getD ""); go { o with verbose := b } seenFile rest
        | "deterministic" => do let b ← boolOpt (val?.getD ""); go { o with deterministic := b } seenFile rest
        | "disable-verify" => do let b ← boolOpt (val?.getD ""); go { o with noVerify := b } seenFile rest
        | "fuse-fmuladd" => do let b ← boolOpt (val?.getD ""); go { o with fuseFMulAdd := b } seenFile rest
        | "use-constant-int-for-fixed-length-splat" | "use-constant-fp-for-fixed-length-splat"
        | "use-constant-int-for-scalable-splat" | "use-constant-fp-for-scalable-splat" =>
          go o seenFile rest
        | _ =>
          match valueOpt name, val? with
          | none, _ => .error s!"Unknown command line argument '{a}'."
          | some set, some v => do go (← set v o) seenFile rest
          | some set, none =>
            match rest with
            | v :: rest' => do go (← set v o) seenFile rest'
            | [] => .error s!"option --{name} requires a value"
      else go { o with file := a } true rest
  termination_by args => args.length

/-! ### Nondeterminism: `std::mt19937_64` -/

/-- The first `n` outputs of `std::mt19937_64` seeded with `seed` (as `llubi`'s `Rng`). -/
def mt19937_64 (seed : UInt64) (n : Nat) : Array UInt64 := Id.run do
  let nn := 312
  let mm := 156
  let matrixA : UInt64 := 0xB5026F5AA96619E9
  let um : UInt64 := 0xFFFFFFFF80000000
  let lm : UInt64 := 0x7FFFFFFF
  let mut mt : Array UInt64 := Array.replicate nn 0
  mt := mt.set! 0 seed
  for i in [1:nn] do
    let prev := mt[i - 1]!
    mt := mt.set! i ((6364136223846793005 : UInt64) * (prev ^^^ (prev >>> 62)) + i.toUInt64)
  let mut idx := nn
  let mut out : Array UInt64 := Array.mkEmpty n
  for _ in [0:n] do
    if idx ≥ nn then
      for i in [0:nn] do
        let x := (mt[i]! &&& um) ||| (mt[(i + 1) % nn]! &&& lm)
        let xA := (x >>> 1) ^^^ (if x &&& 1 == 1 then matrixA else 0)
        mt := mt.set! i (mt[(i + mm) % nn]! ^^^ xA)
      idx := 0
    let mut y := mt[idx]!
    idx := idx + 1
    y := y ^^^ ((y >>> 29) &&& 0x5555555555555555)
    y := y ^^^ ((y <<< 17) &&& 0x71D67FFFEDA60000)
    y := y ^^^ ((y <<< 37) &&& 0xFFF7EEE000000000)
    y := y ^^^ (y >>> 43)
    out := out.push y
  return out

/-! ### Source tables -/

def iidKey (fn : FunctionId) : InstructionId → String
  | .id (.name s) => s!"{fn}|n:{s}"
  | .id (.anonymous n) => s!"{fn}|a:{n}"
  | .void n => s!"{fn}|v:{n}"

/-- Printed instruction text and 0-based source line of every instruction, keyed by `iidKey`. -/
structure SrcTables where
  text   : Std.HashMap String String := {}
  line   : Std.HashMap String Nat := {}
  params : Std.HashMap String (List String) := {}
  /-- Per-function slot renumbering of anonymous values (`%N`). -/
  slots  : Std.HashMap String (List (Nat × Nat)) := {}

/-- LLVM slot numbers of a function's anonymous arguments, blocks and instructions. -/
def computeLocalSlots (toks : Array Tok) (fs : FnSrc) (d : Definition) : List (Nat × Nat) := Id.run do
  let mut slot := 0
  let mut acc : List (Nat × Nat) := []
  for a in d.args do
    match a with
    | .anonymous n => acc := acc ++ [(n, slot)]; slot := slot + 1
    | _ => pure ()
  let entryUnlabeled := match fs.entries[0]? with
    | some e => e.startTok > 0 && toks.getD (e.startTok - 1) .eof == .lbrace
    | none => false
  let mut first := true
  for b in d.blocks do
    match b.id with
    | .anonymous n => acc := acc ++ [(n, slot)]; slot := slot + 1
    | _ => if first && entryUnlabeled then slot := slot + 1
    first := false
    for (iid, _) in b.code do
      match iid with
      | .id (.anonymous n) => acc := acc ++ [(n, slot)]; slot := slot + 1
      | _ => pure ()
  return acc

/-- Canonical key of the metadata node whose definition starts at token `i` (the `!` / `distinct`). -/
private def mdKeyAt (w : WCtx) (i : Nat) : String :=
  match w.tok i with
  | .ident "distinct" => s!"distinct#{i}"
  | .bang => (mdRefAt w i).1
  | _ => s!"node#{i}"

/-- Collect metadata definitions `!name = <node>`. -/
private def collectMdDefs (w : WCtx) : List (String × String) := Id.run do
  let mut acc : List (String × String) := []
  for i in [0:w.toks.size] do
    match w.tok i, w.tok (i + 1) with
    | .metaId nm, .eq =>
      -- only top-level definitions (preceded by nothing or by a non-comma token on a new item)
      acc := acc ++ [(nm, mdKeyAt w (i + 2))]
    | _, _ => pure ()
  return acc

/-- The numbers llubi prints for metadata nodes (`!range !3`). They are the order in which the IR
parser creates `MDNode`s, which this replays over the module's tokens:

* an inline node `!{...}` is created when its closing brace is reached (after the nodes it
  contains), and uniqued: a node with the same content reuses the earlier node (and number);
* a numbered definition `!N = !{...}` likewise (`distinct` nodes are never uniqued);
* the first reference to a numbered node *before* its definition creates a temporary node
  (forward reference), which also takes a number;
* named metadata `!name = !{...}` creates no node.

Established against the pinned llubi on modules with inline nodes, definitions before and after
their uses, uniquing, and nested (TBAA) nodes. Returns node key (as `mdRefAt` computes it) to
number. -/
private def computeMdSlots (w : WCtx) (_fnSrcs : Array FnSrc) : List (String × Nat) := Id.run do
  let isNum (s : String) := !s.isEmpty && s.all Char.isDigit
  let mut slots : List (String × Nat) := []
  let mut defined : List String := []
  let mut temped : List String := []
  let mut next := 0
  -- open metadata brackets: (start position, kind, closed by `}` (true) or `)` (false)); kind is
  -- `inline` | `def N` | `distinct N` | `named` | `plain`
  let mut stack : List (Nat × String × Bool) := []
  -- the kind of a node whose first token (`!` of `!{`, or `!Name` of `!Name(`) is at `k`
  let kindAt (k : Nat) : String :=
    if k ≥ 1 && w.tok (k - 1) == .eq then
      match w.tok (k - 2) with
      | .metaId nm => if isNum nm then "def " ++ nm else "named"
      | _ => "inline"
    else if k ≥ 2 && w.tok (k - 1) == .ident "distinct" && w.tok (k - 2) == .eq then
      match w.tok (k - 3) with
      | .metaId nm => "distinct " ++ nm
      | _ => "inline"
    else "inline"
  for i in [0:w.toks.size] do
    match w.tok i with
    | .metaId m =>
      if isNum m then
        if w.tok (i + 1) != .eq && !defined.contains m && !temped.contains m then
          temped := m :: temped
          next := next + 1
      else if w.tok (i + 1) == .lparen then
        -- a specialized node `!DIFile(...)` (its `(` is the next token)
        stack := (i, kindAt i, false) :: stack
    | .lbrace =>
      if i > 0 && w.tok (i - 1) == .bang then
        stack := (i - 1, kindAt (i - 1), true) :: stack
      else if !stack.isEmpty then
        stack := (i, "plain", true) :: stack
    | .lparen =>
      let isNodeParen := i > 0 && (match w.tok (i - 1) with
        | .metaId m => !isNum m
        | _ => false)
      if !isNodeParen && !stack.isEmpty then
        stack := (i, "plain", false) :: stack
    | .rbrace | .rparen =>
      let isBrace := w.tok i == .rbrace
      match stack with
      | (start, kind, closer) :: rest =>
        if closer == isBrace then
          stack := rest
          let key := if kind.startsWith "def " then
              ((w.mdDefs.find? (·.1 == (kind.drop 4).toString)).map (·.2)).getD ("!" ++ (kind.drop 4).toString)
            else if kind.startsWith "distinct " then
              ((w.mdDefs.find? (·.1 == (kind.drop 9).toString)).map (·.2)).getD ("!" ++ (kind.drop 9).toString)
            else (mdRefAt w start).1
          if kind == "inline" || kind.startsWith "def " then
            if !slots.any (·.1 == key) then
              slots := slots ++ [(key, next)]; next := next + 1
          else if kind.startsWith "distinct " then
            slots := slots ++ [(key, next)]; next := next + 1
          if kind.startsWith "def " then defined := (kind.drop 4).toString :: defined
          if kind.startsWith "distinct " then defined := (kind.drop 9).toString :: defined
      | [] => pure ()
    | _ => pure ()
  return slots

/-- Parse `attributes #N = { ... }` groups. -/
def collectAttrGroups (w : WCtx) : List (Nat × List String) := Id.run do
  let mut acc : List (Nat × List String) := []
  for i in [0:w.toks.size] do
    match w.tok i, w.tok (i + 1), w.tok (i + 2), w.tok (i + 3) with
    | .ident "attributes", .attrGrp n, .eq, .lbrace =>
      let (attrs, _) := collectAttrs w (i + 4)
      acc := acc ++ [(n, attrs)]
    | _, _, _, _ => pure ()
  return acc

/-- `intrinsicAttrIndexText` as a list. -/
private def intrinsicAttrIndex : List (String × Nat) :=
  (intrinsicAttrIndexText.splitOn "\n").filterMap fun l =>
    match l.splitOn "=" with
    | [n, i] => i.toNat?.map (n, ·)
    | _ => none

/-- The attribute set LLVM attaches to the declaration of intrinsic `name` (overloads not in the
table use an entry with the same base name, e.g. `llvm.smax.i16` that of `llvm.smax.i32`). -/
def intrinsicAttrsOf? (name : String) : Option String :=
  let idx? := match intrinsicAttrIndex.find? (·.1 == name) with
    | some (_, i) => some i
    | none =>
      let parts := name.splitOn "."
      (List.range (parts.length - 1)).reverse.findSome? fun k =>
        if k < 2 then none
        else
          let pre := ".".intercalate (parts.take k) ++ "."
          (intrinsicAttrIndex.find? (fun (p : String × Nat) => p.1.startsWith pre)).map (fun (p : String × Nat) => p.2)
  idx?.bind (intrinsicAttrSets[·]?)

/-- Function-attribute keys of all function headers (`define`/`declare`), in module order.
Intrinsic declarations carry the attributes LLVM gives them (`intrinsicAttrsOf?`), which the
slot tracker counts even when the source writes none. -/
def functionAttrKeys (w : WCtx) : List String := Id.run do
  let mut acc : List String := []
  for i in [0:w.toks.size] do
    match w.tok i with
    | .ident "define" | .ident "declare" =>
      -- skip to the parameter list of the first `@name (`, then past its closing parenthesis
      let mut j := i + 1
      while j < w.toks.size && !(match w.tok j with | .globalId _ => w.tok (j + 1) == .lparen | _ => false) do
        j := j + 1
      let fname := match w.tok j with | .globalId (.name n) => n | _ => ""
      j := j + 2
      let mut depth := 1
      while j < w.toks.size && depth > 0 do
        match w.tok j with
        | .lparen => depth := depth + 1
        | .rparen => depth := depth - 1
        | _ => pure ()
        j := j + 1
      let (attrs, _) := collectAttrs w j
      let attrs := match (if fname.startsWith "llvm." then intrinsicAttrsOf? fname else none) with
        | some text => (collectAttrs { w with toks := (AST.Parser.tokenizeWithLines text).1 } 0).1
        | none => attrs
      if !attrs.isEmpty then
        let key := attrSetKey w attrs
        if !acc.contains key then acc := acc ++ [key]
    | _ => pure ()
  return acc

/-- Replace `#⟦key⟧` attribute-set markers by `#N` slot numbers (function attribute sets first,
then call-site sets in order of appearance, as LLVM's slot tracker numbers them). -/
def numberAttrGroups (fnKeys : List String) (texts : List (String × String)) : List (String × String) := Id.run do
  let mut keys := fnKeys
  let mut out : List (String × String) := []
  for (k, t) in texts do
    let mut t' := t
    let mut guard := 8
    while guard > 0 && (t'.splitOn "#⟦").length > 1 do
      guard := guard - 1
      match t'.splitOn "#⟦" with
      | pre :: rest =>
        let restStr := "#⟦".intercalate rest
        match restStr.splitOn "⟧" with
        | key :: after =>
          if !keys.contains key then keys := keys ++ [key]
          let n := keys.idxOf key
          t' := pre ++ s!"#{n}" ++ "⟧".intercalate after
        | [] => guard := 0
      | [] => guard := 0
    out := out ++ [(k, t')]
  return out

/-- Default alignment LLVM attaches to `alloca`/`load`/`store` without an explicit `align`. -/
def defaultAlignOf (dl : DataLayout) : Instruction → Option Nat
  | .alloca ty _ a? _ => some (a?.getD (dl.typePrefAlign ty))
  | .load ty _ _ a? .. => some (a?.getD (dl.typeABIAlign ty))
  | .store ty _ _ _ a? .. => some (a?.getD (dl.typeABIAlign ty))
  | _ => none

/-- Build the printed text / line tables for all instructions of the module. -/
def buildSrcTables (w : WCtx) (pm : ParsedModule) (fns : AssocMap FunctionId Definition) : SrcTables := Id.run do
  let mut t : SrcTables := {}
  for fs in pm.fnSrcs do
    let instrs : List (InstructionId × Instruction) :=
      match fns.get? fs.name with
      | some d => d.blocks.foldl (fun acc b => acc ++ b.code) []
      | none => []
    let slots := match fns.get? fs.name with
      | some d => computeLocalSlots pm.tokens fs d
      | none => []
    let w := { w with localSlots := slots }
    t := { t with slots := t.slots.insert fs.name.toString slots }
    for e in fs.entries do
      let k := iidKey fs.name e.iid
      let hints : InstrHints :=
        match instrs.find? (·.1 == e.iid) with
        | some (_, ins) => { defaultAlign? := defaultAlignOf pm.dataLayout ins }
        | none => {}
      t := { t with text := t.text.insert k (printInstruction w e.startTok e.endTok hints (some e.iid)),
                    line := t.line.insert k e.line }
    t := { t with params := t.params.insert fs.name.toString (printParams w fs.paramsStart fs.paramsEnd) }
  -- resolve attribute-group markers in source order of the instructions
  let ordered : List (String × String) := pm.fnSrcs.toList.foldl (fun acc fs =>
    acc ++ fs.entries.toList.map fun e =>
      let k := iidKey fs.name e.iid
      (k, t.text.getD k "")) []
  for (k, txt) in numberAttrGroups (functionAttrKeys w) ordered do
    t := { t with text := t.text.insert k txt }
  return t

/-! ### Trace driver -/

structure DState where
  tables   : SrcTables
  dl       : DataLayout
  modName  : String
  verbose  : Bool

private def errLine (s : String) : IO Unit := do
  let h ← IO.getStderr
  h.putStr (s ++ "\n")
  h.flush

private def outStr (s : String) : IO Unit := do
  let h ← IO.getStdout
  h.putStr s
  h.flush

/-- One piece of `llubi` output: a line on stderr, or raw text on stdout. -/
inductive TraceOut where
  | stderr (line : String)
  | stdout (text : String)

/-- Sink for trace output. The trace driver is generic in the monad, so the same code streams to
the terminal (`IO`, via `TraceOut.toIO`) and is reasoned about (`traceLoop_result`). -/
abbrev Emit (m : Type → Type) := TraceOut → m Unit

/-- Write a piece of output to the process's stderr/stdout (flushing, so traces interleave). -/
def TraceOut.toIO : TraceOut → IO Unit
  | .stderr s => errLine s
  | .stdout s => outStr s

private def errLn {m : Type → Type} (emit : Emit m) (s : String) : m Unit := emit (.stderr s)
private def outS {m : Type → Type} (emit : Emit m) (s : String) : m Unit := emit (.stdout s)

private def textOf (d : DState) (fn : FunctionId) (iid : InstructionId) : String :=
  d.tables.text.getD (iidKey fn iid) "  <unknown instruction>"

/-- Current (pending) instruction of a frame. -/
private def pendingOf (fr : CallFrame) : InstructionId × (Instruction ⊕ Terminator) :=
  match fr.remainingCode with
  | (iid, ins) :: _ => (iid, .inl ins)
  | [] => (fr.terminator.1, .inr fr.terminator.2)

/-- Print `Stacktrace:` with one line per frame (innermost first). The innermost frame shows its
pending instruction unless `topIsSite` (then every frame shows its waiting call site). -/
private def dumpStackTrace {m : Type → Type} [Monad m] (emit : Emit m) (d : DState)
    (frames : List CallFrame) (callSites : List InstructionId) (topIsSite : Bool := false) : m Unit := do
  errLn emit "Stacktrace:"
  let mut idx := 0
  let sites : List (Option InstructionId) :=
    if topIsSite then callSites.map some else none :: callSites.map some
  for (fr, site?) in frames.zip sites do
    let fn := fr.defn.prototype.name
    let iid := match site? with
      | some s => s
      | none => (pendingOf fr).1
    let k := iidKey fn iid
    let loc := match d.tables.line.get? k with
      | some l => s!" {d.modName}:{l + 1}"
      | none => ""
    errLn emit s!"#{idx} {textOf d fn iid} at {printRawId "@" fn}{loc}"
    idx := idx + 1

/-- llubi's UB messages end with a period, except those that end with a value: the
signature-mismatch, alloca-size and `srem`-overflow reports. -/
private def withPeriod (msg : String) : String :=
  if msg.endsWith "." then msg
  else if (msg.splitOn "mismatched signature. Expected: ").length > 1 ||
      msg.startsWith "Alloca with allocation size that " ||
      msg.startsWith "Signed division overflow. LHS: " then msg
  else msg ++ "."

/-- Library calls whose output must appear before the call's trace line. -/
private def libOutput? (st : MachineState) (fr : CallFrame) (ins : Instruction) (o : OracleState) :
    Option String :=
  match ins with
  | .call _ _ (.identifier (.global_id g)) args .. =>
    let nm := g.toString
    if (st.functions.get? g).isSome || !st.allowLibcallsFor g then none
    else if nm == "puts" || nm == "printf" || nm == "putchar" then
      match execCallArgs st.dataLayout st.config fr.registers st.memory args o with
      | .ok (vals, _, _) =>
        match nm, vals with
        | "puts", [.ptr _ (.value p)] =>
          match readCStringPure st.memory p with
          | .ok s => some (s ++ "\n")
          | .error _ => none
        | "putchar", [.bv _ (.value b)] => some (String.singleton (Char.ofNat (b.toNat % 256)))
        | "printf", .ptr _ (.value p) :: rest =>
          match readCStringPure st.memory p with
          | .ok fmt => renderPrintf st.dataLayout rest.length fmt.length fmt.toList rest st.memory ""
          | .error _ => none
        | _, _ => none
      | .error _ => none
    else none
  | _ => none

/-- Base name of an intrinsic (`llvm.vp.load.v4i32.p0` → `llvm.vp.load`). -/
private def intrinsicBase (nm : String) : String :=
  let bases := intrinsicOverloads.map (·.1)
  match bases.filter (fun b => nm == b || nm.startsWith (b ++ ".")) |>.foldl
      (fun (acc : Option String) b => match acc with
        | some a => if b.length > a.length then some b else acc
        | none => some b) none with
  | some b => b
  | none => nm

/-- `llubi` reports violated value metadata (`!noundef`, `!dereferenceable`, ...) with its own
wording; the semantics shares the parameter-attribute checks and their wording. -/
private def metadataWording (msg : String) : String :=
  if msg.endsWith " violates noundef attribute." then
    (msg.dropEnd " violates noundef attribute.".length).toString ++ " violates !noundef metadata."
  else
    match msg.splitOn " violates dereferenceable_or_null(" with
    | [pre, post] =>
      let n := (post.splitOn ")").head!
      pre ++ s!" violates !dereferenceable_or_null!\{i64 {n}} metadata."
    | _ =>
      match msg.splitOn " violates dereferenceable(" with
      | [pre, post] =>
        let n := (post.splitOn ")").head!
        pre ++ s!" violates !dereferenceable !\{i64 {n}} metadata."
      | _ => msg

/-- Phrase a diagnostic the semantics reports generically the way `llubi` does, using the context
of the instruction that raised it (alloca/byval sizes, intrinsic names and operand values). -/
private def contextualMessage (st : MachineState) (fr : CallFrame) (o : OracleState)
    (pend : Instruction ⊕ Terminator) (msg : String) : String :=
  let dl := st.dataLayout
  match pend with
  | .inl (.alloca ty numEl? _ _) =>
    if msg.startsWith "Allocation size " then
      let elemSz := dl.typeAllocSize ty
      match numEl? with
      | some (nTy, nExp) =>
        match execExp dl st.config fr.registers st.memory nTy nExp o with
        | .ok (.bv _ (.value bv), _, _) =>
          if bv.toNat ≥ 2 ^ 64 then s!"Alloca with large array size that overflows uint64_t. Size: {bv.toInt}"
          else if elemSz * bv.toNat ≥ 2 ^ 64 then s!"Alloca with allocation size that overflows uint64_t. Size: {bv.toInt}"
          else s!"Alloca with allocation size that exceeds the maximum object size. Size: {elemSz * bv.toNat}"
        | _ => msg
      | none => s!"Alloca with allocation size that exceeds the maximum object size. Size: {elemSz}"
    else msg
  | .inl (.call _ _ callee args ..) =>
    let calleeName := match callee with
      | .identifier (.global_id g) => g.toString
      | _ => ""
    let base := intrinsicBase calleeName
    if msg.startsWith "Allocation size " then
      match args.findSome? (fun (_, _, attrs) => attrs.findSome? fun | .byval t => some t | _ => none) with
      | some t => s!"Byval argument with size that exceeds the maximum object size. Size: {dl.typeAllocSize t}"
      | none => msg
    else if msg.startsWith calleeName && calleeName != base && msg.endsWith "is not supported." then
      base ++ (msg.drop calleeName.length).toString
    else if msg.startsWith "Misaligned memory access" &&
        (base.startsWith "llvm.vp." || base.startsWith "llvm.masked." ||
         base.startsWith "llvm.experimental.vp.") then
      "Invalid memory access with a poison pointer."
    else if base.startsWith "llvm.experimental.vp.strided" && msg.endsWith "with poison stride." then
      "Invalid memory access with a poison pointer."
    else if msg.startsWith "poison mask lane in" then s!"Poison mask lane in {base}."
    else if msg.startsWith "poison stride/volatile in" || msg.startsWith "poison stride in" then
      if base.startsWith "llvm.experimental.vp.strided" then "Invalid memory access with a poison pointer."
      else s!"{base} with poison stride."
    else if msg.startsWith "poison evl in" then s!"{base} with poison explicit vector length."
    else if msg.startsWith "evl exceeds vector length in" then
      match execCallArgs dl st.config fr.registers st.memory args o with
      | .ok (vals, _, _) =>
        let evl := match vals.getLast? with
          | some (.bv _ (.value b)) => b.toNat
          | _ => 0
        let n := vals.findSome? (fun | .vector _ es => some es.length | _ => none)
        let n := match n, args.head? with
          | some k, _ => k
          | none, _ => 0
        -- the result vector (loads) determines the element count when no vector operand exists
        s!"{base} with explicit vector length {evl} greater than the number of elements {n}."
      | .error _ => msg
    else msg
  | .inl (.load ..) => metadataWording msg
  | _ => msg

inductive Outcome where
  | returned (v : RegisterValue)
  | failed
  | exited (code : Nat)
  | aborted

/-- How `llubi` reports a final configuration: a return value, `exit(N)` (as an exit status),
`abort()`, or a failure (UB, an error, or running out of steps or memory). -/
def Outcome.ofConfig : Config → Outcome
  | .halted v _ => .returned v
  | .staticError msg =>
    if msg.startsWith "Program exited with code " then
      let codeStr := (msg.drop "Program exited with code ".length).toString
      let code : Int := match codeStr.toInt? with | some i => i | none => 0
      .exited ((code % 256).toNat)
    else if msg == "Program aborted." || msg == "Program terminated." then .aborted
    else .failed
  | _ => .failed


/-- Print the phi nodes at the start of the block a frame just jumped to. -/
private def printPhis {m : Type → Type} [Monad m] (emit : Emit m) (d : DState) (mem : MemoryState)
    (fr : CallFrame) (tags : List (Nat × Nat)) : m Unit := do
  match fr.defn.findBlock? fr.curBlock with
  | some blk =>
    for (iid, ins) in blk.code do
      match ins, iid with
      | .phi .., .id rid =>
        match fr.registers.get? (.local_id rid) with
        | some v => errLn emit s!"{textOf d fr.defn.prototype.name iid} => {v.llubiString mem d.dl tags}"
        | none => pure ()
      | _, _ => pure ()
  | none => pure ()

/-- Print `Entering function:` and its argument lines for a freshly pushed frame. -/
def printEntry {m : Type → Type} [Monad m] (emit : Emit m) (d : DState) (mem : MemoryState)
    (fr : CallFrame) (tags : List (Nat × Nat)) (varArgs : List RegisterValue := []) : m Unit := do
  let fn := fr.defn.prototype.name
  errLn emit s!"Entering function: {fn.toString}"
  let params := d.tables.params.getD fn.toString []
  for (arg, ptxt) in fr.defn.args.zip params do
    match fr.registers.get? (.local_id arg) with
    | some v => errLn emit s!"  {ptxt} = {v.llubiString mem d.dl tags}"
    | none => pure ()
  -- the variadic arguments, as llubi prints them on entry (`vaarg[i] = <typed value>`)
  for (v, i) in varArgs.zip (List.range varArgs.length) do
    errLn emit s!"  vaarg[{i}] = {v.llubiString mem d.dl tags}"

/-- Report a failure (`Stacktrace:` + message). -/
private def reportFailure {m : Type → Type} [Monad m] (emit : Emit m) (d : DState)
    (frames : List CallFrame) (sites : List InstructionId) (msg : String) (topIsSite : Bool := false) :
    m Unit := do
  dumpStackTrace emit d frames sites topIsSite
  errLn emit msg

/-- `llubi`'s wording for running out of memory, which depends on what was being allocated. -/
private def oomMessage (pend : Instruction ⊕ Terminator) : String :=
  match pend with
  | .inl (.alloca ..) => "Error: Insufficient stack space."
  | .inl (.call _ _ _ args ..) =>
    if args.any (fun (_, _, attrs) => attrs.any fun | .byval _ => true | _ => false) then
      "Error: Insufficient stack space for byval pointer argument."
    else "Error: Insufficient heap space."
  | _ => "Error: Insufficient heap space."

/-- Output of a step from `st` to the running configuration `c'`; returns the updated call-site
bookkeeping (`sites`: the call waiting in each caller frame; `byvals`: each callee's byval copies). -/
private def emitRunning {m : Type → Type} [Monad m] (emit : Emit m) (d : DState) (o : OracleState) (st : MachineState)
    (c' : Config) (o' : OracleState) (sites : List InstructionId) (byvals : List (List AllocId)) :
    m (List InstructionId × List (List AllocId)) := do
  match st.frames with
  | [] => return (sites, byvals)
  | fr :: _ =>
    let fn := fr.defn.prototype.name
    let (iid, pend) := pendingOf fr
    let out? := match pend with
      | .inl ins => libOutput? st fr ins o
      | .inr _ => none
    match c' with
    | .running st' =>
      let n := st.frames.length
      let n' := st'.frames.length
      if n' == n + 1 then
        if d.verbose then
          match st'.frames with
          | callee :: _ =>
            -- values of the arguments past the callee's fixed parameters (evaluated in the caller)
            let isVarArgFn := match callee.defn.prototype.type with
              | .function _ _ va => va
              | _ => false
            let varArgs : List RegisterValue := match pend with
              | .inl (.call _ _ _ args ..) =>
                if !isVarArgFn then [] else
                (args.drop callee.defn.args.length).filterMap fun (ty, e, _) =>
                  match execExp st.dataLayout st.config fr.registers st.memory ty e o with
                  | .ok (v, _, _) => some v
                  | .error _ => none
              | _ => []
            printEntry emit d st'.memory callee o'.tags varArgs
          | [] => pure ()
        -- objects created while entering the callee are its byval copies
        let copies := (List.range (st'.memory.nextAllocId - st.memory.nextAllocId)).map
          (· + st.memory.nextAllocId)
        return Prod.mk (iid :: sites) (copies :: byvals)
      else if n' + 1 == n then
        -- returned from a callee into its caller
        if d.verbose then
          errLn emit (textOf d fn iid)
          errLn emit s!"Exiting function: {fn.toString}"
          match sites, st'.frames with
          | site :: _, caller :: _ =>
            let ctext := textOf d caller.defn.prototype.name site
            match site with
            | .id rid =>
              -- llubi reports the call's result before releasing the callee's byval copies
              let memShown := (byvals.headD []).foldl (fun (m : MemoryState) id =>
                match m.objects.get? id with
                | some obj => { m with objects := m.objects.insert id { obj with state := .alive } }
                | none => m) st'.memory
              match caller.registers.get? (.local_id rid) with
              | some v => errLn emit s!"{ctext} => {v.llubiString memShown d.dl o'.tags}"
              | none => errLn emit ctext
            | .void _ => errLn emit ctext
          | _, _ => pure ()
        return Prod.mk sites.tail byvals.tail
      else
        match pend with
        | .inl _ =>
          if let some s := out? then outS emit s
          -- `callbr` is a terminator in LLVM: it is reported once, with its jump
          if d.verbose && !(textOf d fn iid).startsWith "  callbr " then
            match iid, st'.frames with
            | .id rid, fr' :: _ =>
              match fr'.registers.get? (.local_id rid) with
              | some v => errLn emit s!"{textOf d fn iid} => {v.llubiString st'.memory d.dl o'.tags}"
              | none => errLn emit (textOf d fn iid)
            | _, _ => errLn emit (textOf d fn iid)
          return Prod.mk sites byvals
        | .inr _ =>
          if d.verbose then
            match st'.frames with
            | fr' :: _ =>
              let w : WCtx := { toks := #[], dl := d.dl, typeDefs := [], mdDefs := [], mdSlots := [],
                                fnTypes := [], localSlots := d.tables.slots.getD fn.toString [] }
              errLn emit s!"{textOf d fn iid} jump to {w.loc fr'.curBlock}"
              printPhis emit d st'.memory fr' o'.tags
            | [] => pure ()
          return Prod.mk sites byvals
    | _ => return (sites, byvals)

/-- Output of a step from `st` to the final configuration `c'` (return, UB, error, exit). -/
private def emitStop {m : Type → Type} [Monad m] (emit : Emit m) (d : DState) (o : OracleState)
    (st : MachineState) (c' : Config) (sites : List InstructionId) :
    m Unit := do
  match st.frames with
  | [] => return ()
  | fr :: _ =>
    let fn := fr.defn.prototype.name
    let (iid, pend) := pendingOf fr
    match c' with
    | .halted _ _ =>
      if d.verbose then
        errLn emit (textOf d fn iid)
        errLn emit s!"Exiting function: {fn.toString}"
      return ()
    | .ub msg0 =>
      let msg := contextualMessage st fr o pend msg0
      match pend, st.frames with
      | .inr (.ret _), _ :: callers@(_ :: _) | .inr .retVoid, _ :: callers@(_ :: _) =>
        -- return-time checks happen in the caller after the callee has exited
        if d.verbose then
          errLn emit (textOf d fn iid)
          errLn emit s!"Exiting function: {fn.toString}"
        reportFailure emit d callers sites s!"Immediate UB detected: {withPeriod msg}" (topIsSite := true)
      | .inr term, _ =>
        -- UB while evaluating phi nodes happens after `llubi` has reported the jump
        let dest? : Option BlockId := match term with
          | .br b => some b
          | .condBr c t f =>
            match execExp st.dataLayout st.config fr.registers st.memory .i1 c o with
            | .ok (.bv 1 (.value b), _, _) => some (if b.toNat == 1 then t else f)
            | _ => none
          | .switch ty c dflt cases =>
            match execExp st.dataLayout st.config fr.registers st.memory ty c o with
            | .ok (.bv w (.value bv), _, _) =>
              some ((cases.find? (fun (cv, _) => BitVec.ofInt w cv == bv)).map (·.2) |>.getD dflt)
            | _ => none
          | _ => none
        let destHasPhi := match dest? with
          | some b => match fr.defn.findBlock? b with
            | some blk => blk.code.any fun | (_, .phi ..) => true | _ => false
            | none => false
          | none => false
        match dest? with
        | some b =>
          if destHasPhi then
            let w : WCtx := { toks := #[], dl := d.dl, typeDefs := [], mdDefs := [], mdSlots := [],
                              fnTypes := [], localSlots := d.tables.slots.getD fn.toString [] }
            if d.verbose then errLn emit s!"{textOf d fn iid} jump to {w.loc b}"
            -- the failing phi is reported at the head of the destination block
            let phiIid := match fr.defn.findBlock? b with
              | some blk => (blk.code.head?.map (·.1)).getD iid
              | none => iid
            errLn emit "Stacktrace:"
            let k := iidKey fn phiIid
            let loc := match d.tables.line.get? k with
              | some l => s!" {d.modName}:{l + 1}"
              | none => ""
            errLn emit s!"#0 {textOf d fn phiIid} at {printRawId "@" fn}{loc}"
            let mut idx := 1
            for (cfr, site) in st.frames.tail.zip sites do
              let ck := iidKey cfr.defn.prototype.name site
              let cloc := match d.tables.line.get? ck with
                | some l => s!" {d.modName}:{l + 1}"
                | none => ""
              errLn emit s!"#{idx} {textOf d cfr.defn.prototype.name site} at {printRawId "@" cfr.defn.prototype.name}{cloc}"
              idx := idx + 1
            errLn emit s!"Immediate UB detected: {withPeriod (metadataWording msg)}"
            return ()
          else reportFailure emit d st.frames sites s!"Immediate UB detected: {withPeriod msg}"
        | none => reportFailure emit d st.frames sites s!"Immediate UB detected: {withPeriod msg}"
      | _, _ => reportFailure emit d st.frames sites s!"Immediate UB detected: {withPeriod msg}"
    | .staticError msg =>
      if msg.startsWith "Call to undefined external function" then
        errLn emit s!"Unrecognized instruction: {textOf d fn iid}"
        return ()
      else
      if msg.startsWith "Program exited with code " then
        let codeStr := (msg.drop "Program exited with code ".length).toString
        let code : Int := match codeStr.toInt? with | some i => i | none => 0
        if d.verbose then errLn emit s!"Program exited with code {code}"
        return ()
      else if msg == "Program aborted." || msg == "Program terminated." then
        if d.verbose then errLn emit msg
        return ()
      else
        reportFailure emit d st.frames sites s!"Error: {withPeriod (contextualMessage st fr o pend msg)}"
    | .resourceError .outOfMemory =>
      reportFailure emit d st.frames sites (oomMessage pend)
    | .resourceError .stackOverflow =>
      reportFailure emit d st.frames sites "Error: Maximum stack depth exceeded."
    | .resourceError .outOfFuel =>
      reportFailure emit d st.frames sites "Error: Exceeded maximum number of execution steps."
    | .resourceError (.immediateUB msg) =>
      reportFailure emit d st.frames sites s!"Immediate UB detected: {withPeriod msg}"
    | .resourceError (.staticError msg) =>
      reportFailure emit d st.frames sites s!"Error: {withPeriod msg}"
    | .running _ => return ()

/-- Output for a configuration that is already final before any step. -/
private def emitFinal {m : Type → Type} [Monad m] (emit : Emit m) (d : DState) : Config → m Unit
  | .halted .. | .running _ => pure ()
  | .ub msg => errLn emit s!"Immediate UB detected: {withPeriod msg}"
  | c@(.staticError msg) =>
    match Outcome.ofConfig c with
    | .exited _ | .aborted => if d.verbose then errLn emit msg else pure ()
    | _ => errLn emit s!"Error: {withPeriod msg}"
  | .resourceError _ => errLn emit "Error: Out of memory."

/-- Main trace loop: run `execStep` for at most `fuel` steps (`llubi`'s `--max-steps`), emitting the
`--verbose` trace and diagnostics, and return the final configuration and oracle state. The
configuration it returns is exactly that of the formal semantics' `runSteps` (`traceLoop_result`);
`Outcome.ofConfig` of it is the run's outcome. -/
def traceLoop {m : Type → Type} [Monad m] (emit : Emit m) :
    Nat → DState → OracleState → Config → List InstructionId → List (List AllocId) →
      m (Config × OracleState)
  | 0, d, o, c@(.running st), sites, _ => do
    if !st.frames.isEmpty then
      reportFailure emit d st.frames sites "Error: Exceeded maximum number of execution steps."
    pure (c, o)
  | fuel + 1, d, o, c@(.running st), sites, byvals => do
    let (_, c', o') := execStep o c
    match c' with
    | .running _ =>
      let (sites', byvals') ← emitRunning emit d o st c' o' sites byvals
      traceLoop emit fuel d o' c' sites' byvals'
    | _ =>
      emitStop emit d o st c' sites
      pure (c', o')
  | _, d, o, c, _, _ => do
    emitFinal emit d c
    pure (c, o)

/-! ### The trace driver runs the formal semantics -/

private theorem runSteps_succ_running' (n : Nat) (o : OracleState) (st : MachineState) (r)
    (h : execStep o (.running st) = r) :
    (runSteps (n + 1) o (.running st)).2 = (runSteps n r.2.2 r.2.1).2 := by
  obtain ⟨ora, idx, nid, tg⟩ := o
  obtain ⟨frames, mem, cfg, dl, fns, decls⟩ := st
  obtain ⟨ev, c1, ⟨ora1, idx1, nid1, tg1⟩⟩ := r
  dsimp only [runSteps]
  rw [h]
  cases ev <;> rfl

private theorem runSteps_zero (o : OracleState) (c : Config) : runSteps 0 o c = ([], c, o) := rfl

private theorem runSteps_final (n : Nat) (o : OracleState) (c : Config) (h : ∀ st, c ≠ .running st) :
    (runSteps n o c).2 = (c, o) := by
  cases n with
  | zero => rfl
  | succ n => cases c with
    | running st => exact absurd rfl (h st)
    | _ => rfl

/-- **The `llubi` frontend executes exactly the formal semantics.** Whatever monad the trace is
emitted into (`IO` included) and whatever it prints, `traceLoop` with `fuel` steps returns the
configuration and oracle state that `runSteps` (the kernel-reducible small-step driver of the
semantics) reaches in `fuel` steps. The `llubi` exit status is a function of that configuration
(`Outcome.ofConfig`), so only the printed text (stack traces, instruction lines) lies outside the
theorem; the byte-for-byte comparison against `llubi` covers it. -/
theorem traceLoop_result {m : Type → Type} [Monad m] [LawfulMonad m] (emit : Emit m)
    (fuel : Nat) (d : DState) (o : OracleState) (c : Config) (sites : List InstructionId)
    (byvals : List (List AllocId)) :
    (fun _ => (runSteps fuel o c).2) <$> traceLoop emit fuel d o c sites byvals =
      traceLoop emit fuel d o c sites byvals := by
  induction fuel generalizing o c sites byvals with
  | zero =>
    rw [runSteps_zero]
    cases c <;> simp only [traceLoop, map_bind, map_pure]
    split <;> simp only [map_bind, map_pure]
  | succ n ih =>
    cases c with
    | running st =>
      rw [runSteps_succ_running' n o st _ rfl]
      simp only [traceLoop]
      rcases hs : execStep o (.running st) with ⟨ev, c', o'⟩
      cases c' with
      | running st' =>
        simp only [map_bind]
        congr 1; funext x
        exact ih o' (.running st') x.1 x.2
      | _ =>
        simp only [map_bind, map_pure]
        rw [runSteps_final]
        intro _ h; cases h
    | _ =>
      simp only [traceLoop, map_bind, map_pure]
      rw [runSteps_final]
      intro _ h; cases h

/-- Corollary: the outcome (`llubi`'s exit status) the frontend reports is the outcome of the
formal semantics' `runSteps` run. -/
theorem traceLoop_outcome {m : Type → Type} [Monad m] [LawfulMonad m] (emit : Emit m)
    (fuel : Nat) (d : DState) (o : OracleState) (c : Config) (sites : List InstructionId)
    (byvals : List (List AllocId)) :
    (fun r => Outcome.ofConfig r.1) <$> traceLoop emit fuel d o c sites byvals =
      (fun _ => Outcome.ofConfig (runSteps fuel o c).2.1) <$> traceLoop emit fuel d o c sites byvals := by
  conv => lhs; rw [← traceLoop_result]
  simp [Functor.map_map]

/-! ### Entry point -/

private def mkConfig (o : Options) : SemanticsConfig :=
  let base : SemanticsConfig := {
    undefMode := .nondet, freezeMode := .nondet, nanMode := .nondet,
    maxSteps := o.maxSteps, maxStackDepth := o.maxStackDepth, maxMem := o.maxMem,
    vscale := o.vscale, fuseFMulAdd := o.fuseFMulAdd }
  let base := match o.nanMode with
    | "preferred" => { base with nanMode := .preferred }
    | "quieting" => { base with nanMode := .quieting }
    | "unchanged" => { base with nanMode := .unchanged }
    | _ => base
  let base := match o.undefMode? with
    | some "zero" => { base with undefMode := .zero }
    | _ => base
  if o.deterministic then
    { base with undefMode := .zero, freezeMode := .zero, nanMode := .preferred }
  else base

private def isPowerOf2 (n : Nat) : Bool := n != 0 && (n &&& (n - 1)) == 0

/-- `llubi` main: returns the process exit code. -/
def llubiMain (args : List String) : IO UInt32 := do
  match parseOptions args with
  | .error msg =>
    errLine s!"llubi: {msg}"
    return 1
  | .ok opts =>
  if opts.entry.isEmpty then
    errLine "error: --entry-function name cannot be empty"; return 1
  if opts.vscale == 0 then
    errLine "error: --vscale value must be positive"; return 1
  if !isPowerOf2 opts.vscale then
    errLine "error: --vscale value must be a power of 2"; return 1
  let src ← if opts.file == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile opts.file
  let modName := if opts.file == "-" then "<stdin>" else opts.file
  match Parser.parseLlvmModule src opts.vscale with
  | .error msg =>
    errLine s!"llubi: {modName}: error: {msg}"
    return 1
  | .ok pm =>
  let cfg0 := mkConfig opts
  let tr := pm.dataLayout.targetTriple
  let cfg :=
    if opts.nanMode == "target-specific" && !opts.deterministic then
      { cfg0 with nanMode :=
          if tr.startsWith "sparc" then .sparcPreferred
          else if tr.startsWith "wasm" then .wasm
          else .preferred }
    else cfg0
  -- Static verification subset (`verifyModule`)
  if !opts.noVerify then
    let hasBadPhi := pm.topLevel.entities.any fun
      | .definition defn =>
        defn.blocks.any fun blk =>
          blk.code.any fun (_, instr) =>
            match instr with
            | .phi _ _ inc _ => inc.any fun (e1, b1) => inc.any fun (e2, b2) => b1 == b2 && e1.print != e2.print
            | _ => false
      | _ => false
    if hasBadPhi then
      errLine "PHINode should have one entry for each predecessor of its parent basic block!"
      errLine s!"error: {modName}: input module is broken!"
      return 1
  let rng := mt19937_64 opts.seed.toUInt64 65536
  let oracle : OracleState :=
    if opts.deterministic then default
    else { oracle := fun i => (rng[i]?.getD 0).toNat }
  match initModuleExec pm.topLevel cfg pm.dataLayout oracle with
  | .error _ =>
    errLine "error: Failed to initialize global values (e.g., the memory limit may be too low)."
    return 1
  | .ok (mem, fns, decls, o1) =>
  let mut o1 := o1
  match fns.get? (.name opts.entry) with
  | none =>
    if (decls.get? (.name opts.entry)).isSome then
      errLine s!"error: '{opts.entry}' must be definition."
    else
      errLine s!"error: '{opts.entry}' function not found in module."
    return 1
  | some defn =>
  let dl := pm.dataLayout
  -- Build `argc`/`argv` exactly as llubi does.
  let argv0 := if opts.fakeArgv0.isEmpty then
      (if opts.file.endsWith ".bc" then (opts.file.dropEnd 3).toString else opts.file)
    else opts.fakeArgv0
  let inputArgv := argv0 :: opts.progArgs
  let (retTy, paramTys) := match defn.prototype.type with
    | .function r ps _ => (r, ps)
    | _ => (.void, [])
  let isMainSig := retTy == .ret (.int 32) && paramTys == [.int 32, .ptr 0]
  let mut mem := mem
  let mut entryArgs : List RegisterValue := []
  if isMainSig then
    let ptrSz := (dl.getPointerSizeInBits 0 + 7) / 8
    match mem.allocate dl cfg (ptrSz * (inputArgv.length + 1)) 8 "argv" 0 .zeroed .global false with
    | .error _ =>
      errLine "error: Failed to allocate memory for argv pointers."; return 1
    | .ok (argvObj, m1) =>
      mem := m1
      let mut idx := 0
      for a in inputArgv do
        let bytes := a.toUTF8
        match mem.allocate dl cfg (bytes.size + 1) 8 "argv_str" 0 .zeroed .global false with
        | .error _ =>
          errLine "error: Failed to allocate memory for argv strings."; return 1
        | .ok (strObj, m2) =>
          let raw : Array MemByte := bytes.toList.toArray.map MemByte.concrete
          let m3 := m2.writeObjectBytes strObj.allocId 0 raw
          let argPtr : RegisterValue := .ptr 0 (.value (MemoryState.derivePointer dl strObj))
          o1 := drawPtrTags argPtr o1
          let pbytes := valueToBytes dl cfg argPtr (.ptr 0)
          mem := m3.writeObjectBytes argvObj.allocId (idx * ptrSz) pbytes
        idx := idx + 1
      entryArgs := [.bv 32 (.value (BitVec.ofNat 32 inputArgv.length)),
                    .ptr 0 (.value (MemoryState.derivePointer dl argvObj))]
  else if !paramTys.isEmpty then
    errLine s!"warning: The signature of function '{opts.entry}' does not match 'int main(int, char**)', passing null values for all arguments."
    entryArgs := paramTys.map (RegisterValue.nullOf dl)
  -- Printing tables
  let typeDefs : List (RawId × PTy) := pm.topLevel.entities.filterMap fun
    | .typeDef nm ty => some (nm, PTy.ofLlvmType ty)
    | _ => none
  let fnTypes : List (String × LlvmType) := pm.topLevel.entities.filterMap fun
    | .declaration decl => some (decl.name.toString, decl.type)
    | .definition d => some (d.prototype.name.toString, d.prototype.type)
    | _ => none
  let w0 : WCtx := { toks := pm.tokens, dl, typeDefs, mdDefs := [], mdSlots := [], fnTypes,
                     vscale := opts.vscale }
  let w0 := { w0 with attrGroupDefs := collectAttrGroups w0 }
  let w1 := { w0 with mdDefs := collectMdDefs w0 }
  let w := { w1 with mdSlots := computeMdSlots w1 pm.fnSrcs }
  let tables := buildSrcTables w pm fns
  let d : DState := { tables, dl, modName, verbose := opts.verbose }
  let initCfg := initCallConfig cfg dl mem fns decls defn entryArgs
  -- Function entry for the entry point
  if opts.verbose then
    match initCfg with
    | .running st =>
      match st.frames with
      | fr :: _ => printEntry TraceOut.toIO d st.memory fr o1.tags
      | [] => pure ()
    | _ => pure ()
  -- `--max-steps=0` means unbounded; `2^62` steps is unbounded in practice and stays a scalar
  let fuel := if opts.maxSteps == 0 then 2 ^ 62 else opts.maxSteps
  let (cFinal, _) ← traceLoop TraceOut.toIO fuel d o1 initCfg [] []
  match Outcome.ofConfig cFinal with
  | .failed =>
    errLine s!"error: Execution of function '{opts.entry}' failed."
    return 1
  | .aborted => return 134
  | .exited code => return code.toUInt32
  | .returned v =>
    match retTy with
    | .ret (.int _) =>
      match v with
      | .bv _ .poison =>
        errLine s!"error: Execution of function '{opts.entry}' resulted in poison return value."
        return 1
      | .bv w (.value b) => return (b.toNat % (2 ^ (min w 8))).toUInt32
      | _ => return 0
    | _ => return 0

end LeanNanoLlvm.Llubi
