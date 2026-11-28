import LeanNanoLlvm.AST.Parser
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.AST.FloatLiteral

/-!
# Source-faithful LLVM `AsmWriter` emulation

`llubi --verbose` prints every executed instruction with LLVM's `Instruction::print`.  To reproduce
that text exactly, this module re-prints each instruction from its *source tokens* (recorded by the
parser's source map) while applying the canonicalizations that parsing into `llvm::Module` and
printing back performs:

* integer constants are printed as signed values of their type (`i1` as `true`/`false`);
* floating-point constants use `writeAPFloatInternal` (`1.500000e+00`, `+qnan`, `f0x3D4CCCC8`, ...);
* aggregate constants are uniqued (`zeroinitializer`, `poison`, `undef`, `splat (T v)`, `c"..."`);
* `alloca`/`load`/`store` get their implicit `align` (computed from the resolved AST + data layout);
* intrinsic immediate arguments get `/* ... */` comments (`llvm.is.fpclass`), metadata attachments
  are renumbered as LLVM's slot tracker does, and calls only print their function type when the
  callee is variadic;
* `switch` is laid out over multiple lines.

Everything here is executable code used by the `llubi` frontend; it has no role in the formal
semantics. It is nevertheless total: recursion over types and constants is structural (or
well-founded on `sizeOf`), and the token-level printers are structural on a fuel budget
(`WCtx.fuel`), following the convention of `AST.Parser`.
-/

namespace LeanNanoLlvm.Llubi

open LeanNanoLlvm.AST
open LeanNanoLlvm.AST.Parser

/-! ### Identifiers -/

private def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '$' || c == '.' || c == '_'

/-- `PrintLLVMName`: print `name` with prefix `sigil`, quoting it when necessary. -/
def printLLVMName (sigil : String) (name : String) : String :=
  let needsQuote :=
    name.isEmpty || !(name.all isNameChar) || (name.front.isDigit && !(name.all Char.isDigit))
  if needsQuote then
    let esc := name.foldl (fun acc c =>
      if c == '"' || c == '\\' || c.toNat < 32 || c.toNat > 126 then
        acc ++ "\\" ++ Hex.upperPadded 2 (c.toNat % 256)
      else acc.push c) ""
    sigil ++ "\"" ++ esc ++ "\""
  else sigil ++ name

def printRawId (sigil : String) : RawId → String
  | .anonymous n => sigil ++ toString n
  | .name s => printLLVMName sigil s

/-! ### Printable types -/

/-- Type as written in the source (keeps scalable vectors, named types and `label`). -/
inductive PTy where
  | int (w : Nat)
  | byte (w : Nat)
  | float (ft : FloatType)
  | ptr (addrSpace : Nat)
  | void | label | metadata | token | opaque
  | vec (scalable : Bool) (n : Nat) (elem : PTy)
  | arr (n : Nat) (elem : PTy)
  | struct (packed : Bool) (fields : List PTy)
  | named (nm : RawId)
  | fn (ret : PTy) (params : List PTy) (isVarArg : Bool)
  | other (s : String)
deriving Inhabited, BEq, Repr

def PTy.print : PTy → String
  | .int w => s!"i{w}"
  | .byte w => s!"b{w}"
  | .float ft => ft.print
  | .ptr 0 => "ptr"
  | .ptr as => s!"ptr addrspace({as})"
  | .void => "void"
  | .label => "label"
  | .metadata => "metadata"
  | .token => "token"
  | .opaque => "opaque"
  | .vec sc n e => if sc then s!"<vscale x {n} x {e.print}>" else s!"<{n} x {e.print}>"
  | .arr n e => s!"[{n} x {e.print}]"
  | .struct false [] => "{}"
  | .struct true [] => "<{}>"
  | .struct false fs => "{ " ++ ", ".intercalate (fs.map PTy.print) ++ " }"
  | .struct true fs => "<{ " ++ ", ".intercalate (fs.map PTy.print) ++ " }>"
  | .named nm => printRawId "%" nm
  | .fn r ps va =>
    let args := ps.map PTy.print ++ (if va then ["..."] else [])
    s!"{r.print} ({", ".intercalate args})"
  | .other s => s

def PTy.ofLlvmType : LlvmType → PTy
  | .int w => .int w
  | .byte w => .byte w
  | .float ft => .float ft
  | .ptr as => .ptr as
  | .vector n e => .vec false n (PTy.ofLlvmType e)
  | .array n e => .arr n (PTy.ofLlvmType e)
  | .struct p fs => .struct p (fs.map PTy.ofLlvmType)
  | .named nm => .named nm
  | .function r ps va =>
    .fn (match r with | .void => .void | .ret t => PTy.ofLlvmType t) (ps.map PTy.ofLlvmType) va

/-! ### Writer context -/

/-- Static context for printing instructions of one module. -/
structure WCtx where
  toks      : Array Tok
  dl        : DataLayout
  /-- Named struct definitions (as written). -/
  typeDefs  : List (RawId × PTy)
  /-- Metadata definitions `!N = ...`: name ↦ canonical content key. -/
  mdDefs    : List (String × String)
  /-- LLVM slot numbers for metadata nodes, keyed by canonical content. -/
  mdSlots   : List (String × Nat)
  /-- Declared/defined function types (for variadic call printing). -/
  fnTypes   : List (String × LlvmType)
  vscale    : Nat := 4
  /-- Tokens at or beyond `limit` read as `eof` (0 = unbounded). -/
  limit     : Nat := 0
  /-- Slot renumbering of anonymous local values/blocks of the current function (`%N`). -/
  localSlots : List (Nat × Nat) := []
  /-- Attribute groups `attributes #N = { ... }` (canonically ordered attribute strings). -/
  attrGroupDefs : List (Nat × List String) := []

def WCtx.tok (c : WCtx) (i : Nat) : Tok :=
  if c.limit != 0 && i ≥ c.limit then .eof else c.toks.getD i .eof

/-- Print a local identifier, renumbering anonymous values as LLVM's slot tracker does. -/
def WCtx.loc (c : WCtx) : RawId → String
  | .anonymous n => "%" ++ toString ((c.localSlots.find? (·.1 == n)).map (·.2) |>.getD n)
  | id => printRawId "%" id

/-- Recursion budget of the token-level printers below. Each recursive call spends one unit, and
every chain of calls consumes a source token at least every few calls, so the budget is never the
limiting factor on real input; it only makes termination structural (no `partial`). -/
def WCtx.fuel (c : WCtx) : Nat := 4 * (c.toks.size + 1)

/-- Resolve named types to their structural definition (bounded depth). -/
def WCtx.resolve (c : WCtx) (t : PTy) (depth : Nat := 16) : PTy :=
  match t, depth with
  | .named _, 0 => t
  | .named nm, depth + 1 =>
    match c.typeDefs.find? (·.1 == nm) with
    | some (_, d) => c.resolve d depth
    | none => t
  | _, _ => t

/-! ### Constant values -/

/-- A parsed operand / constant, prior to canonical printing. -/
inductive CVal where
  | raw     (s : String)                 -- identifiers and anything printed verbatim
  | int     (v : Int)
  | fpBits  (bits : Nat)                 -- `IEEEFloat` bits in the semantic format of the type
  | fpDec   (neg : Bool) (m : Nat) (e : Int)
  | fpSpec  (neg isInf quiet : Bool) (payload : Nat)
  | bool    (b : Bool)
  | null | zero | undef | poison | none
  | str     (bytes : List Nat)
  | agg     (elems : List (PTy × CVal))  -- array / vector / struct elements
  | splat   (ty : PTy) (v : CVal)
  | expr    (s : String)                 -- constant expression (already printed)
deriving Inhabited, BEq, Repr

private def fpOf (ft : FloatType) : CVal → Option (IEEEFloat ft.format)
  | .fpBits b => some (IEEEFloat.ofNatBits b)
  | .fpDec n m e => some (IEEEFloat.ofDecimal ft.format .RNE n m e)
  | .fpSpec n isInf q p =>
    some (if isInf then IEEEFloat.inf ft.format n
          else if q then IEEEFloat.qNaN ft.format n p
          else IEEEFloat.sNaN ft.format n (if p == 0 then 1 else p))
  | .int v => some (IEEEFloat.ofDecimal ft.format .RNE (v < 0) v.natAbs 0)
  | _ => none

/-- Decode a hexadecimal float literal of tag `tag` for type `ft` into semantic `IEEEFloat` bits. -/
def decodeHexFloat (ft : FloatType) (tag : Char) (val : Nat) : Nat :=
  match ft, tag with
  | .float, 'd' | .half, 'd' | .bfloat, 'd' =>
    -- exact conversion; NaNs keep their signaling bit and top payload (`IEEEFloat.narrowFromDoubleHex`)
    (IEEEFloat.narrowFromDoubleHex ft.format val).bits.toNat
  | .x86_fp80, 'K' =>
    -- drop the explicit integer bit (bit 63) of the 80-bit encoding
    let sig := val &&& ((1 <<< 63) - 1)
    let rest := val >>> 64
    (rest <<< 63) ||| sig
  | .fp128, 'L' =>
    let first := val >>> 64
    let second := val &&& ((1 <<< 64) - 1)
    (second <<< 64) ||| first
  | .ppc_fp128, 'M' =>
    let hi := val >>> 64
    let lo := val &&& ((1 <<< 64) - 1)
    (lo <<< 64) ||| hi
  | _, _ => val

/-- An element of an aggregate constant is smaller than the aggregate (termination measure for the
structural recursions below, which recurse through `List.map`/`List.all`). -/
theorem CVal.sizeOf_lt_agg {p : PTy × CVal} {es : List (PTy × CVal)} (h : p ∈ es) :
    sizeOf p.2 < sizeOf (CVal.agg es) := by
  have := List.sizeOf_lt_of_mem h
  cases p; simp_all; omega

namespace CVal

/-- `Constant::isNullValue` for a value of type `t`. -/
def isNull (c : WCtx) (t : PTy) : CVal → Bool
  | .zero | .null => true
  | .bool b => !b
  | .int v =>
    match c.resolve t with
    | .float ft => match fpOf ft (.int v) with | some f => f.bits.toNat == 0 | _ => false
    | _ => v == 0
  | .fpBits b => b == 0
  | v@(.fpDec ..) =>
    match c.resolve t with
    | .float ft => match fpOf ft v with | some f => f.bits.toNat == 0 | _ => false
    | _ => false
  | .str bs => bs.all (· == 0)
  | .agg es => es.attach.all fun ⟨p, _⟩ => p.2.isNull c p.1
  | .splat et v => v.isNull c et
  | _ => false
termination_by v => v
decreasing_by
  · exact CVal.sizeOf_lt_agg ‹_›
  · simp_wf; omega

def isPoison : CVal → Bool
  | .poison => true
  | _ => false

/-- Element is a simple `ConstantInt` / `ConstantFP` / `ConstantByte`. -/
def isSimple : CVal → Bool
  | .int _ | .fpBits _ | .fpDec .. | .fpSpec .. | .bool _ => true
  | _ => false

end CVal

private def elemOf (c : WCtx) (t : PTy) (i : Nat) : PTy :=
  match c.resolve t with
  | .vec _ _ e | .arr _ e => e
  | .struct _ fs => fs.getD i .void
  | _ => .void

/-- Canonicalize a constant the way `llvm::Constant` uniquing does. -/
def canon (c : WCtx) (t : PTy) (v : CVal) : CVal :=
  match v with
  | .agg es0 =>
    let es := es0.attach.map fun ⟨p, _⟩ => (p.1, canon c p.1 p.2)
    let rt := c.resolve t
    match rt with
    | .struct _ _ =>
      if es.isEmpty then .zero
      else if es.all (fun (et, ev) => ev.isNull c et) then .zero
      else if es.all (fun (_, ev) => ev.isPoison) then .poison
      else if es.all (fun (_, ev) => ev == .undef) then .undef
      else .agg es
    | _ =>
      match es with
      | [] => .zero
      | (_, first) :: _ =>
        let allSame := es.all (fun (_, ev) => ev == first)
        if allSame && first.isPoison then .poison
        else if allSame && first == .undef then .undef
        else if allSame && first.isNull c (elemOf c t 0) then
          (match rt with
           | .vec _ _ (.ptr as) => .splat (.ptr as) .null
           | _ => .zero)
        else
          match rt with
          | .arr _ (.int 8) =>
            if es.all (fun (_, ev) => match ev with | .int _ => true | _ => false) then
              .str (es.map fun (_, ev) => match ev with | .int i => (i % 256).toNat | _ => 0)
            else .agg es
          | .vec _ _ e =>
            if allSame && first.isSimple then .splat e first else .agg es
          | _ => .agg es
  | .zero =>
    match c.resolve t with
    | .vec _ _ (.ptr as) => .splat (.ptr as) .null
    | _ => .zero
  | .str bs =>
    if bs.all (· == 0) then .zero else .str bs
  | .splat et ev =>
    let ev' := canon c et ev
    if ev'.isPoison then .poison
    else if ev' == .undef then .undef
    else if ev'.isNull c et then
      (match et with
       | .ptr _ => .splat et .null
       | _ => .zero)
    else if ev'.isSimple then .splat et ev'
    else
      match c.resolve t with
      | .vec false n _ => .agg (List.replicate n (et, ev'))
      | _ => .splat et ev'
  | other => other
termination_by v
decreasing_by all_goals first | exact CVal.sizeOf_lt_agg ‹_› | (simp_wf; omega)

/-- `printEscapedString`. -/
def escapeCString (bytes : List Nat) : String :=
  bytes.foldl (fun acc b =>
    let ch := Char.ofNat b
    if b ≥ 32 && b < 127 && b != 92 && b != 34 then acc.push ch
    else acc ++ "\\" ++ Hex.upperPadded 2 b) ""

/-- Print an integer `v` as a signed value of width `w` (`APInt` printing). -/
def signedOfWidth (w : Nat) (v : Int) : Int :=
  if w == 0 then v else
  let m := v.toNat % (2 ^ w)
  let mn : Int := (v % (2 ^ w : Int))
  let u := if mn < 0 then mn + 2 ^ w else mn
  let _ := m
  if u ≥ 2 ^ (w - 1) then u - 2 ^ w else u

/-- Print a (canonicalized) constant value of type `t` (without the type). -/
def printConst (c : WCtx) (t : PTy) (v : CVal) : String :=
  match v with
  | .raw s => s
  | .expr s => s
  | .null => "null"
  | .zero => "zeroinitializer"
  | .undef => "undef"
  | .poison => "poison"
  | .none => "none"
  | .bool b =>
    match c.resolve t with
    | .int 1 => if b then "true" else "false"
    | .int w => toString (if b then signedOfWidth w 1 else 0)
    | _ => if b then "true" else "false"
  | .int i =>
    match c.resolve t with
    | .int 1 => if i % 2 != 0 then "true" else "false"
    | .int w | .byte w => toString (signedOfWidth w i)
    | .float ft =>
      match fpOf ft (.int i) with
      | some f => FloatLiteral.asmString ft f
      | none => toString i
    | _ => toString i
  | .fpBits _ | .fpDec .. | .fpSpec .. =>
    match c.resolve t with
    | .float ft =>
      match fpOf ft v with
      | some f => FloatLiteral.asmString ft f
      | none => "<float>"
    | _ => "<float>"
  | .str bs => "c\"" ++ escapeCString bs ++ "\""
  | .splat et ev =>
    let evStr := printConst c et ev
    match c.resolve t, ev with
    | .vec true n _, .raw _ | .vec true n _, .expr _ =>
      -- LLVM prints a scalable splat of a non-arithmetic constant as a `shufflevector` expression
      let vt := PTy.vec true n et
      let mt := PTy.vec true n (.int 32)
      s!"shufflevector ({vt.print} insertelement ({vt.print} poison, {et.print} {evStr}, i64 0), {vt.print} poison, {mt.print} zeroinitializer)"
    | _, _ => s!"splat ({et.print} {evStr})"
  | .agg es =>
    let items := es.attach.map fun ⟨p, _⟩ => s!"{p.1.print} {printConst c p.1 p.2}"
    match c.resolve t with
    | .vec .. => "<" ++ ", ".intercalate items ++ ">"
    | .arr .. => "[" ++ ", ".intercalate items ++ "]"
    | .struct true _ => "<{ " ++ ", ".intercalate items ++ " }>"
    | _ => "{ " ++ ", ".intercalate items ++ " }"
termination_by v
decreasing_by all_goals first | exact CVal.sizeOf_lt_agg ‹_› | (simp_wf; omega)

/-! ### Token-level parsing for printing -/

private def isFloatName : String → Option FloatType
  | "half" => some .half
  | "bfloat" => some .bfloat
  | "float" => some .float
  | "double" => some .double
  | "x86_fp80" => some .x86_fp80
  | "fp128" => some .fp128
  | "ppc_fp128" => some .ppc_fp128
  | _ => none

private def widthOf? (pfx : Char) (s : String) : Option Nat :=
  if s.length ≥ 2 && s.front == pfx then (s.drop 1).toString.toNat? else none

mutual

/-- Parse a type starting at token `i` (no function-type suffix). -/
def parseTyAtF (fuel : Nat) (c : WCtx) (i : Nat) : Option (PTy × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match c.tok i with
    | .ident s =>
      if let some ft := isFloatName s then some (.float ft, i + 1)
      else if let some w := widthOf? 'i' s then some (.int w, i + 1)
      else if let some w := widthOf? 'b' s then some (.byte w, i + 1)
      else match s with
        | "ptr" =>
          if c.tok (i + 1) == .ident "addrspace" && c.tok (i + 2) == .lparen then
            match c.tok (i + 3) with
            | .intLit n => some (.ptr n.toNat, i + 5)
            | _ => some (.ptr 0, i + 1)
          else some (.ptr 0, i + 1)
        | "void" => some (.void, i + 1)
        | "label" => some (.label, i + 1)
        | "metadata" => some (.metadata, i + 1)
        | "token" => some (.token, i + 1)
        | "opaque" => some (.opaque, i + 1)
        | "x86_amx" => some (.other "x86_amx", i + 1)
        | _ => none
    | .localId nm =>
      if c.typeDefs.any (·.1 == nm) then some (.named nm, i + 1) else none
    | .langle =>
      match c.tok (i + 1), c.tok (i + 2) with
      | .ident "vscale", .ident "x" =>
        match c.tok (i + 3), c.tok (i + 4) with
        | .intLit n, .ident "x" =>
          match parseTyAtF fuel c (i + 5) with
          | some (e, j) => if c.tok j == .rangle then some (.vec true n.toNat e, j + 1) else none
          | none => none
        | _, _ => none
      | .intLit n, .ident "x" =>
        match parseTyAtF fuel c (i + 3) with
        | some (e, j) => if c.tok j == .rangle then some (.vec false n.toNat e, j + 1) else none
        | none => none
      | _, _ => none
    | .lbrack =>
      match c.tok (i + 1), c.tok (i + 2) with
      | .intLit n, .ident "x" =>
        match parseTyAtF fuel c (i + 3) with
        | some (e, j) => if c.tok j == .rbrack then some (.arr n.toNat e, j + 1) else none
        | none => none
      | _, _ => none
    | .lbrace => parseStructTyF fuel c (i + 1) false
    | .lpacked => parseStructTyF fuel c (i + 1) true
    | _ => none

/-- Parse `T, T, ... }` (or `}>` when packed); fails if a value follows a field type. -/
def parseStructTyF (fuel : Nat) (c : WCtx) (i : Nat) (packed : Bool) : Option (PTy × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let close := if packed then Tok.rpacked else Tok.rbrace
    if c.tok i == close then some (.struct packed [], i + 1)
    else
      let rec go (fuel : Nat) (j : Nat) (acc : List PTy) : Option (PTy × Nat) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseTyAtF fuel c j with
          | some (t, k) =>
            if c.tok k == .comma then go fuel (k + 1) (t :: acc)
            else if c.tok k == close then some (.struct packed (t :: acc).reverse, k + 1)
            else none
          | none => none
      go fuel i []

end

/-- Parse a type starting at token `i` (no function-type suffix). -/
def parseTyAt (c : WCtx) (i : Nat) : Option (PTy × Nat) := parseTyAtF c.fuel c i

/-- Does token `i` start a value (operand / constant)? -/
def startsValue (c : WCtx) (i : Nat) : Bool :=
  match c.tok i with
  | .intLit _ | .fltLit .. | .hexLit .. | .localId _ | .globalId _ | .langle | .lbrack
  | .lbrace | .lpacked | .strLit _ => true
  | .bang | .metaId _ => true
  | .ident s =>
    s.startsWith "u0x" || s.startsWith "s0x" ||
    s ∈ ["true", "false", "null", "undef", "poison", "zeroinitializer", "none", "splat", "c",
         "blockaddress", "dso_local_equivalent", "no_cfi", "getelementptr", "ptrtoint",
         "inttoptr", "bitcast", "addrspacecast", "ptrtoaddr", "trunc", "add", "sub", "mul",
         "xor", "shl", "extractelement", "insertelement", "shufflevector", "+inf", "-inf",
         "+qnan", "-qnan", "+nan", "-nan", "+snan", "-snan", "inf", "qnan", "nan", "snan"]
  | _ => false

private def constExprOps : List String :=
  ["getelementptr", "ptrtoint", "inttoptr", "bitcast", "addrspacecast", "ptrtoaddr", "trunc",
   "add", "sub", "mul", "xor", "shl", "extractelement", "insertelement", "shufflevector"]

private def flagWords : List String :=
  ["nuw", "nsw", "exact", "disjoint", "inbounds", "nusw", "samesign", "nneg", "inrange",
   "fast", "nnan", "ninf", "nsz", "arcp", "contract", "afn", "reassoc"]

/-- Canonical order of instruction flags (as LLVM's `writeOptimizationInfo`). -/
def canonFlags (fs : List String) : List String :=
  let has (f : String) := fs.contains f
  let fmfAll := ["reassoc", "nnan", "ninf", "nsz", "arcp", "contract", "afn"]
  let fmf :=
    if has "fast" || fmfAll.all has then ["fast"]
    else fmfAll.filter has
  let wrap := (if has "disjoint" then ["disjoint"] else []) ++
    (if has "exact" then ["exact"] else []) ++
    (if has "inbounds" then ["inbounds"] else if has "nusw" then ["nusw"] else []) ++
    (if has "nuw" then ["nuw"] else []) ++ (if has "nsw" then ["nsw"] else []) ++
    (if has "nneg" then ["nneg"] else []) ++ (if has "samesign" then ["samesign"] else [])
  wrap ++ fmf

/-- Collect flag words starting at `i`. -/
def collectFlagsF (fuel : Nat) (c : WCtx) (i : Nat) (acc : List String := []) : List String × Nat :=
  match fuel with
  | 0 => (acc, i)
  | fuel + 1 =>
    match c.tok i with
    | .ident s => if flagWords.contains s then collectFlagsF fuel c (i + 1) (acc ++ [s]) else (acc, i)
    | _ => (acc, i)

/-- `collectFlagsF` with the full recursion budget `c.fuel`. -/
def collectFlags (c : WCtx) (i : Nat) (acc : List String := []) : List String × Nat :=
  collectFlagsF c.fuel c i (acc := acc)

/-- Canonical metadata reference text for `!name` / inline `!{...}` at token `i`. -/
def mdRefAt (c : WCtx) (i : Nat) : String × Nat :=
  match c.tok i with
  | .metaId nm =>
    let key := (c.mdDefs.find? (·.1 == nm)).map (·.2) |>.getD ("!" ++ nm)
    match c.mdSlots.find? (·.1 == key) with
    | some (_, n) => (s!"!{n}", i + 1)
    | none => ("!" ++ nm, i + 1)
  | .bang =>
    -- inline node `!{ ... }`
    let rec skip (fuel : Nat) (j : Nat) (depth : Nat) (acc : String) : String × Nat :=
      match fuel with
      | 0 => (acc, j)
      | fuel + 1 =>
        match c.tok j with
        | .lbrace => skip fuel (j + 1) (depth + 1) (acc ++ "{")
        | .rbrace => if depth ≤ 1 then (acc ++ "}", j + 1) else skip fuel (j + 1) (depth - 1) (acc ++ "}")
        | .eof => (acc, j)
        | t => skip fuel (j + 1) depth (acc ++ reprStr t)
    let (key, j) := skip c.fuel (i + 1) 0 "!"
    match c.mdSlots.find? (·.1 == key) with
    | some (_, n) => (s!"!{n}", j)
    | none => (key, j)
  | _ => ("", i + 1)
where
  reprStr : Tok → String
    | .intLit n => s!" {n}"
    | .ident s => s!" {s}"
    | .comma => ","
    | .strLit s => s!" \"{s}\""
    | .metaId m => s!" !{m}"
    | _ => " ?"

/-- Decode the raw (escape-preserving) contents of a `c"..."` literal into bytes. -/
def decodeCStr (s : String) : List Nat :=
  let rec go : List Char → List Nat
    | [] => []
    | '\\' :: a :: b :: rest =>
      let hv (ch : Char) : Option Nat :=
        if ch.isDigit then some (ch.toNat - '0'.toNat)
        else if 'a' ≤ ch && ch ≤ 'f' then some (ch.toNat - 'a'.toNat + 10)
        else if 'A' ≤ ch && ch ≤ 'F' then some (ch.toNat - 'A'.toNat + 10)
        else none
      match hv a, hv b with
      | some x, some y => (x * 16 + y) :: go rest
      | _, _ => if a == '\\' then 92 :: go (b :: rest) else a.toNat :: go (b :: rest)
    | '\\' :: '\\' :: rest => 92 :: go rest
    | ch :: rest =>
      -- UTF-8 encode
      let n := ch.toNat
      if n < 0x80 then n :: go rest
      else if n < 0x800 then (0xC0 ||| (n >>> 6)) :: (0x80 ||| (n &&& 0x3F)) :: go rest
      else if n < 0x10000 then
        (0xE0 ||| (n >>> 12)) :: (0x80 ||| ((n >>> 6) &&& 0x3F)) :: (0x80 ||| (n &&& 0x3F)) :: go rest
      else
        (0xF0 ||| (n >>> 18)) :: (0x80 ||| ((n >>> 12) &&& 0x3F)) ::
          (0x80 ||| ((n >>> 6) &&& 0x3F)) :: (0x80 ||| (n &&& 0x3F)) :: go rest
  termination_by l => l.length
  go s.toList

/-- The elements of a fixed vector constant `v : <n x et>`, if it is in a foldable form. -/
def vecElems (c : WCtx) (vt : PTy) (n : Nat) (et : PTy) (v : CVal) :
    Option (List (PTy × CVal)) :=
  let nullOf : CVal := match c.resolve et with
    | .int _ | .byte _ => .int 0
    | .float _ => .fpBits 0
    | .ptr _ => .null
    | _ => .zero
  match canon c vt v with
  | .agg es => some es
  | .zero => some (List.replicate n (et, nullOf))
  | .poison => some (List.replicate n (et, .poison))
  | .undef => some (List.replicate n (et, .undef))
  | .splat t v => some (List.replicate n (t, v))
  | _ => none

mutual

/-- Parse a value of type `t` at token `i`. -/
def parseValAtF (fuel : Nat) (c : WCtx) (t : PTy) (i : Nat) : Option (CVal × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let rt := c.resolve t
    match c.tok i with
    | .intLit n =>
      match rt with
      | .float _ => some (.int n, i + 1)
      | _ => some (.int n, i + 1)
    | .fltLit neg m e => some (.fpDec neg m e, i + 1)
    | .hexLit tag v =>
      match rt with
      | .float ft => some (.fpBits (decodeHexFloat ft tag v), i + 1)
      | _ => some (.int v, i + 1)
    | .localId id => some (.raw (c.loc id), i + 1)
    | .globalId id => some (.raw (printRawId "@" id), i + 1)
    | .metaId _ | .bang =>
      let (s, j) := mdRefAt c i
      some (.raw s, j)
    | .ident s =>
      match s with
      | "true" => some (.bool true, i + 1)
      | "false" => some (.bool false, i + 1)
      | "null" => some (.null, i + 1)
      | "undef" => some (.undef, i + 1)
      | "poison" => some (.poison, i + 1)
      | "zeroinitializer" => some (.zero, i + 1)
      | "none" => some (.none, i + 1)
      | "c" =>
        match c.tok (i + 1) with
        | .strLit str => some (.str (decodeCStr str), i + 2)
        | _ => none
      | "splat" =>
        if c.tok (i + 1) == .lparen then
          match parseTyAt c (i + 2) with
          | some (et, j) =>
            match parseValAtF fuel c et j with
            | some (ev, k) => if c.tok k == .rparen then some (.splat et ev, k + 1) else none
            | none => none
          | none => none
        else none
      | "blockaddress" =>
        match c.tok (i + 1), c.tok (i + 2), c.tok (i + 3), c.tok (i + 4), c.tok (i + 5) with
        | .lparen, .globalId f, .comma, .localId b, .rparen =>
          some (.raw s!"blockaddress({printRawId "@" f}, {c.loc b})", i + 6)
        | _, _, _, _, _ => none
      | "dso_local_equivalent" | "no_cfi" =>
        match c.tok (i + 1) with
        | .globalId f => some (.raw s!"{s} {printRawId "@" f}", i + 2)
        | _ => none
      | "+inf" | "inf" => some (.fpSpec false true false 0, i + 1)
      | "-inf" => some (.fpSpec true true false 0, i + 1)
      | "+qnan" | "qnan" => some (.fpSpec false false true 0, i + 1)
      | "-qnan" => some (.fpSpec true false true 0, i + 1)
      | "+nan" | "nan" | "-nan" | "+snan" | "snan" | "-snan" =>
        let neg := s.startsWith "-"
        let quiet := !(s.endsWith "snan")
        match c.tok (i + 1), c.tok (i + 2), c.tok (i + 3) with
        | .lparen, .hexLit _ p, .rparen => some (.fpSpec neg false quiet p, i + 4)
        | .lparen, .intLit p, .rparen => some (.fpSpec neg false quiet p.toNat, i + 4)
        | _, _, _ => some (.fpSpec neg false quiet 0, i + 1)
      | _ =>
        if (s.startsWith "u0x" || s.startsWith "s0x") && s.length > 3 then
          let hex := (s.drop 3).toString
          let v := hex.foldl (fun acc ch =>
            let d := if ch.isDigit then ch.toNat - '0'.toNat
              else if 'a' ≤ ch && ch ≤ 'f' then ch.toNat - 'a'.toNat + 10
              else if 'A' ≤ ch && ch ≤ 'F' then ch.toNat - 'A'.toNat + 10 else 0
            acc * 16 + d) 0
          some (.int v, i + 1)
        else if s == "insertelement" && (foldInsertElementF fuel c (i + 1)).isSome then
          foldInsertElementF fuel c (i + 1)
        else if s == "shufflevector" && (foldShuffleVectorF fuel c (i + 1)).isSome then
          foldShuffleVectorF fuel c (i + 1)
        else if constExprOps.contains s then
          match printConstExprF fuel c s (i + 1) with
          | some (str, j) => some (.expr str, j)
          | none => none
        else none
    | .langle =>
      match parseTypedListF fuel c (i + 1) .rangle with
      | some (es, j) => some (.agg es, j)
      | none => none
    | .lbrack =>
      match parseTypedListF fuel c (i + 1) .rbrack with
      | some (es, j) => some (.agg es, j)
      | none => none
    | .lbrace =>
      match parseTypedListF fuel c (i + 1) .rbrace with
      | some (es, j) => some (.agg es, j)
      | none => none
    | .lpacked =>
      match parseTypedListF fuel c (i + 1) .rpacked with
      | some (es, j) => some (.agg es, j)
      | none => none
    | _ => none

/-- `insertelement (<N x T> vec, T elt, Ti k)` of a constant vector at a constant index folds to a
vector constant (LLVM's constant folder); `none` if not foldable. -/
def foldInsertElementF (fuel : Nat) (c : WCtx) (i : Nat) : Option (CVal × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if c.tok i != .lparen then none else
    match parseTyAt c (i + 1) with
    | some (vt@(.vec false n et), j) =>
      match parseValAtF fuel c vt j with
      | some (vv, j2) =>
        if c.tok j2 != .comma then none else
        match parseTyAt c (j2 + 1) with
        | some (et', j3) =>
          match parseValAtF fuel c et' j3 with
          | some (ev, j4) =>
            if c.tok j4 != .comma then none else
            match parseTyAt c (j4 + 1) with
            | some (it, j5) =>
              match parseValAtF fuel c it j5 with
              | some (CVal.int k, j6) =>
                if c.tok j6 != .rparen then none else
                let nullOf : CVal := match c.resolve et with
                  | .int _ | .byte _ => .int 0
                  | .float _ => .fpBits 0
                  | .ptr _ => .null
                  | _ => .zero
                let elems? : Option (List (PTy × CVal)) := match canon c vt vv with
                  | .agg es => some es
                  | .zero => some (List.replicate n (et, nullOf))
                  | .poison => some (List.replicate n (et, .poison))
                  | .undef => some (List.replicate n (et, .undef))
                  | .splat t v => some (List.replicate n (t, v))
                  | _ => none
                match elems? with
                | some es =>
                  if k < 0 || k.toNat ≥ n then some (.poison, j6 + 1)
                  else some (.agg (es.set k.toNat (et, ev)), j6 + 1)
                | none => none
              | _ => none
            | none => none
          | none => none
        | none => none
      | none => none
    | _ => none

/-- `shufflevector (<N x T> v1, <N x T> v2, <M x i32> mask)` of fixed vectors folds to a vector
of per-element `extractelement`s (LLVM's constant folder); `none` if not foldable. -/
def foldShuffleVectorF (fuel : Nat) (c : WCtx) (i : Nat) : Option (CVal × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if c.tok i != .lparen then none else
    match parseTyAt c (i + 1) with
    | some (vt@(.vec false n et), j) =>
      match parseValAtF fuel c vt j with
      | some (v1, j2) =>
        if c.tok j2 != .comma then none else
        match parseTyAt c (j2 + 1) with
        | some (vt2, j3) =>
          match parseValAtF fuel c vt2 j3 with
          | some (v2, j4) =>
            if c.tok j4 != .comma then none else
            match parseTyAt c (j4 + 1) with
            | some (mt@(.vec false m mEt), j5) =>
              match parseValAtF fuel c mt j5 with
              | some (mv, j6) =>
                if c.tok j6 != .rparen then none else
                match vecElems c mt m mEt mv with
                | some mask =>
                  let pick (src : CVal) (k : Nat) : CVal :=
                    match vecElems c vt n et src with
                    | some es => (es.getD k (et, .poison)).2
                    | none => .expr s!"extractelement ({vt.print} {printConst c vt (canon c vt src)}, i32 {k})"
                  let elems := mask.map fun (_, mk) =>
                    match mk with
                    | .int k =>
                      if k < 0 then (et, CVal.poison)
                      else if k.toNat < n then (et, pick v1 k.toNat)
                      else if k.toNat < 2 * n then (et, pick v2 (k.toNat - n))
                      else (et, .poison)
                    | _ => (et, .poison)
                  some (.agg elems, j6 + 1)
                | none => none
              | none => none
            | _ => none
          | none => none
        | none => none
      | none => none
    | _ => none

/-- Parse `T v, T v, ... <close>`. -/
def parseTypedListF (fuel : Nat) (c : WCtx) (i : Nat) (close : Tok) : Option (List (PTy × CVal) × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if c.tok i == close then some ([], i + 1)
    else
      let rec go (fuel : Nat) (j : Nat) (acc : List (PTy × CVal)) : Option (List (PTy × CVal) × Nat) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseTyAt c j with
          | some (t, k) =>
            match parseValAtF fuel c t k with
            | some (v, l) =>
              if c.tok l == .comma then go fuel (l + 1) ((t, v) :: acc)
              else if c.tok l == close then some (((t, v) :: acc).reverse, l + 1)
              else none
            | none => none
          | none => none
      go fuel i []

/-- Print a constant expression `op [flags] (operands [to T])` starting after the opcode. -/
def printConstExprF (fuel : Nat) (c : WCtx) (op : String) (i : Nat) : Option (String × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let (flags, j0) := collectFlags c i
    let flagStr := String.join ((canonFlags flags).map (" " ++ ·))
    if c.tok j0 != .lparen then none
    else
      -- GEP source element type
      let (pre, j1) : String × Nat :=
        if op == "getelementptr" then
          match parseTyAt c (j0 + 1) with
          | some (st, k) => (st.print ++ ", ", if c.tok k == .comma then k + 1 else k)
          | none => ("", j0 + 1)
        else ("", j0 + 1)
      let rec go (fuel : Nat) (j : Nat) (acc : List (PTy × CVal)) : Option (List (PTy × CVal) × Nat) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseTyAt c j with
          | some (t, k) =>
            match parseValAtF fuel c t k with
            | some (v, l) =>
              if c.tok l == .comma then go fuel (l + 1) ((t, canon c t v) :: acc)
              else some (((t, canon c t v) :: acc).reverse, l)
            | none => none
          | none => none
      match go fuel j1 [] with
      | some (ops0, k) =>
        -- A vector GEP splats its scalar indices (LLParser).
        let vecLen? : Option Nat := ops0.findSome? fun (t, _) =>
          match c.resolve t with | .vec false n _ => some n | _ => none
        let ops := match op, vecLen?, ops0 with
          | "getelementptr", some n, base :: idxs =>
            base :: idxs.map fun (t, v) => match c.resolve t with
              | it@(.int _) => (PTy.vec false n it, canon c (.vec false n it) (.splat it v))
              | _ => (t, v)
          | _, _, _ => ops0
        let items := ops.map fun (t, v) => s!"{t.print} {printConst c t v}"
        let (toTy?, k2) : Option PTy × Nat :=
          if c.tok k == .ident "to" then
            match parseTyAt c (k + 1) with
            | some (tt, k3) => (some tt, k3)
            | none => (none, k + 1)
          else (none, k)
        let toStr := match toTy? with | some tt => s!" to {tt.print}" | none => ""
        if c.tok k2 != .rparen then none
        else
          -- LLVM folds a binary operator on fixed vectors into a vector of element operations.
          let binOps := ["add", "sub", "mul", "xor", "shl"]
          let foldBin? : Option (List (PTy × CVal)) :=
            match ops with
            | [(vt@(.vec false n et), a), (_, b)] =>
              if !binOps.contains op || toTy?.isSome then none else
              match vecElems c vt n et a, vecElems c vt n et b with
              | some as, some bs =>
                some ((as.zip bs).map fun ((_, x), (_, y)) =>
                  match x, y, c.resolve et with
                  | .int xi, .int yi, .int w =>
                    if !flags.isEmpty && !(op == "xor") then
                      (et, .expr s!"{op}{flagStr} ({et.print} {printConst c et x}, {et.print} {printConst c et y})")
                    else
                      let m : Int := 2 ^ w
                      let r : Int := match op with
                        | "add" => xi + yi | "sub" => xi - yi | "mul" => xi * yi
                        | "xor" => Int.ofNat ((xi % m).toNat ^^^ (yi % m).toNat)
                        | _ => if yi.toNat < w then xi * 2 ^ yi.toNat else 0
                      let u := r % m
                      (et, .int (if u ≥ m / 2 then u - m else u))
                  | .poison, _, _ | _, .poison, _ => (et, .poison)
                  | _, _, _ =>
                    (et, .expr s!"{op}{flagStr} ({et.print} {printConst c et x}, {et.print} {printConst c et y})"))
              | _, _ => none
            | _ => none
          match foldBin? with
          | some es => some (printConst c (ops.head!.1) (canon c (ops.head!.1) (.agg es)), k2 + 1)
          | none =>
          -- LLVM folds a (non-bitcast) cast of a fixed vector into a vector of element casts
          match toTy?, ops with
          | some (.vec false n dstElem), [(srcTy@(.vec false _ srcElem), v)] =>
            if op == "bitcast" then some (s!"{op}{flagStr} ({pre}{", ".intercalate items}{toStr})", k2 + 1)
            else
              let elems := (List.range n).map fun idx =>
                let srcElemStr := match v with
                  | .agg es => match es[idx]? with
                    | some (et, ev) => s!"{et.print} {printConst c et ev}"
                    | none => s!"{srcElem.print} poison"
                  | _ => s!"{srcElem.print} extractelement ({srcTy.print} {printConst c srcTy v}, i32 {idx})"
                s!"{dstElem.print} {op}{flagStr} ({srcElemStr} to {dstElem.print})"
              some ("<" ++ ", ".intercalate elems ++ ">", k2 + 1)
          | _, _ => some (s!"{op}{flagStr} ({pre}{", ".intercalate items}{toStr})", k2 + 1)
      | none => none

end

/-- Parse a value of type `t` at token `i`. -/
def parseValAt (c : WCtx) (t : PTy) (i : Nat) : Option (CVal × Nat) := parseValAtF c.fuel c t i

/-- Print `T v` canonically. -/
def printTypedOperand (c : WCtx) (t : PTy) (v : CVal) : String :=
  s!"{t.print} {printConst c t (canon c t v)}"

/-- `operator<<(raw_ostream&, FPClassTest)`. -/
def fpClassTestString (mask : Nat) : String :=
  let names : List (Nat × String) :=
    [(1023, "all"), (3, "nan"), (1, "snan"), (2, "qnan"), (516, "inf"), (4, "ninf"), (512, "pinf"),
     (96, "zero"), (32, "nzero"), (64, "pzero"), (144, "sub"), (16, "nsub"), (128, "psub"),
     (264, "norm"), (8, "nnorm"), (256, "pnorm")]
  if mask == 0 then "(none)"
  else
    let (_, parts) := names.foldl (fun (m, acc) (bit, nm) =>
      if m &&& bit == bit then (m - bit, acc ++ [nm]) else (m, acc)) (mask, [])
    "(" ++ " ".intercalate parts ++ ")"

/-! ### Parameter attributes -/

/-- Print one parameter/return attribute starting at token `i`; `none` if `i` is not an attribute. -/
def parseAttrAt (c : WCtx) (i : Nat) : Option (String × Nat) :=
  match c.tok i with
  | .ident s =>
    if startsValue c i then none
    else if parseTyAt c i |>.isSome then none
    else if s == "align" then
      match c.tok (i + 1) with
      | .intLit n => some (s!"align {n}", i + 2)
      | .lparen =>
        match c.tok (i + 2) with
        | .intLit n => some (s!"align {n}", i + 4)
        | _ => some ("align", i + 1)
      | _ => some ("align", i + 1)
    else if c.tok (i + 1) == .lparen then
      -- attribute with argument: byval(T), dereferenceable(N), range(T a, b), nofpclass(...)
      match s with
      | "byval" | "sret" | "byref" | "preallocated" | "inalloca" | "elementtype" =>
        match parseTyAt c (i + 2) with
        | some (t, j) => some (s!"{s}({t.print})", j + 1)
        | none => some (s, i + 1)
      | "range" =>
        match parseTyAt c (i + 2) with
        | some (t, j) =>
          let rec goRange (fuel : Nat) (k : Nat) (acc : List String) : List String × Nat :=
            match fuel with
            | 0 => (acc, k)
            | fuel + 1 =>
              match c.tok k with
              | .intLit n =>
                let acc' := acc ++ [toString (match t with | .int w => signedOfWidth w n | _ => n)]
                if c.tok (k + 1) == .comma then goRange fuel (k + 2) acc' else (acc', k + 1)
              | _ => (acc, k)
          let (vals, k) := goRange c.fuel j []
          some (s!"range({t.print} {", ".intercalate vals})", k + 1)
        | none => some (s, i + 1)
      | "nofpclass" =>
        -- argument is a list of class names; re-encode canonically
        let rec goFpc (fuel : Nat) (k : Nat) (mask : Nat) : Nat × Nat :=
          match fuel with
          | 0 => (mask, k)
          | fuel + 1 =>
            match c.tok k with
            | .ident nm =>
              let bit := match nm with
                | "all" => 1023 | "nan" => 3 | "snan" => 1 | "qnan" => 2 | "inf" => 516
                | "ninf" => 4 | "pinf" => 512 | "zero" => 96 | "nzero" => 32 | "pzero" => 64
                | "sub" => 144 | "nsub" => 16 | "psub" => 128 | "norm" => 264 | "nnorm" => 8
                | "pnorm" => 256 | _ => 0
              goFpc fuel (k + 1) (mask ||| bit)
            | .intLit n => goFpc fuel (k + 1) (mask ||| n.toNat)
            | .rparen => (mask, k + 1)
            | .eof => (mask, k)
            | _ => goFpc fuel (k + 1) mask
        let (mask, k) := goFpc c.fuel (i + 2) 0
        some (s!"nofpclass{fpClassTestString mask}", k)
      | _ =>
        let rec goOther (fuel : Nat) (k : Nat) (depth : Nat) (acc : String) : String × Nat :=
          match fuel with
          | 0 => (acc, k)
          | fuel + 1 =>
            match c.tok k with
            | .lparen => goOther fuel (k + 1) (depth + 1) acc
            | .rparen => if depth ≤ 1 then (acc, k + 1) else goOther fuel (k + 1) (depth - 1) acc
            | .intLit n => goOther fuel (k + 1) depth (if acc.isEmpty then toString n else acc ++ ", " ++ toString n)
            | .eof => (acc, k)
            | _ => goOther fuel (k + 1) depth acc
        let (inner, k) := goOther c.fuel (i + 1) 0 ""
        some (s!"{s}({inner})", k)
    else some (s, i + 1)
  | .attrGrp n => some (s!"#{n}", i + 1)
  | _ => none

/-- Sort key of an attribute as `AttributeSet` orders them: enum attributes, then integer
attributes, then type attributes, then constant-range attributes (each alphabetically), then
string attributes and attribute-group references. (TableGen emits enum, type, int, then
constant-range attribute kinds.) -/
def attrSortKey (a : String) : Nat × String :=
  let nm := (a.splitOn "(").head!.splitOn " " |>.head!
  -- TableGen record names (`Attributes.td`), whose ASCII order defines the enum order
  let recordNames : List (String × String) :=
    [("noundef", "NoUndef"), ("nonnull", "NonNull"), ("noalias", "NoAlias"),
     ("nocapture", "NoCapture"), ("readonly", "ReadOnly"), ("readnone", "ReadNone"),
     ("writeonly", "WriteOnly"), ("signext", "SExt"), ("zeroext", "ZExt"), ("inreg", "InReg"),
     ("returned", "Returned"), ("nofree", "NoFree"), ("nosync", "NoSync"),
     ("nounwind", "NoUnwind"), ("willreturn", "WillReturn"), ("immarg", "ImmArg"),
     ("noreturn", "NoReturn"), ("nest", "Nest"), ("swiftself", "SwiftSelf"),
     ("align", "Alignment"), ("dereferenceable", "Dereferenceable"),
     ("dereferenceable_or_null", "DereferenceableOrNull"), ("nofpclass", "NoFPClass"),
     ("byval", "ByVal"), ("sret", "StructRet"), ("byref", "ByRef"),
     ("elementtype", "ElementType"), ("inalloca", "InAlloca"), ("preallocated", "Preallocated"),
     ("range", "Range"), ("memory", "Memory"), ("captures", "Captures")]
  let rec' := (recordNames.find? (·.1 == nm)).map (·.2) |>.getD
    (String.ofList (nm.toList.mapIdx fun i ch => if i == 0 then ch.toUpper else ch))
  let intAttrs := ["align", "alignstack", "allockind", "allocsize", "captures", "dereferenceable",
    "dereferenceable_or_null", "memory", "nofpclass", "uwtable", "vscale_range"]
  let typeAttrs := ["byref", "byval", "elementtype", "inalloca", "preallocated", "sret"]
  let cls := if a.startsWith "#" then 5 else if a.startsWith "\"" then 4
    else if nm == "range" then 3 else if intAttrs.contains nm then 2
    else if typeAttrs.contains nm then 1 else 0
  (cls, rec')

/-- Collect attributes starting at `i` (returned in LLVM's canonical order). -/
def collectAttrsF (fuel : Nat) (c : WCtx) (i : Nat) (acc : List String := []) : List String × Nat :=
  match fuel with
  | 0 => (acc, i)
  | fuel + 1 =>
    match parseAttrAt c i with
    | some (a, j) => collectAttrsF fuel c j (acc ++ [a])
    | none =>
      (acc.mergeSort (fun a b =>
        let ka := attrSortKey a
        let kb := attrSortKey b
        ka.1 < kb.1 || (ka.1 == kb.1 && ka.2 ≤ kb.2)), i)

/-- `collectAttrsF` with the full recursion budget `c.fuel`. -/
def collectAttrs (c : WCtx) (i : Nat) (acc : List String := []) : List String × Nat :=
  collectAttrsF c.fuel c i (acc := acc)

/-- Canonical key of an attribute set (attribute-group references expanded). -/
def attrSetKey (c : WCtx) (attrs : List String) : String :=
  let expanded := attrs.foldl (fun acc a =>
    if a.startsWith "#" then
      match (a.drop 1).toString.toNat? with
      | some n => match c.attrGroupDefs.find? (·.1 == n) with
        | some (_, as) => acc ++ as
        | none => acc ++ [a]
      | none => acc ++ [a]
    else acc ++ [a]) []
  let sorted := expanded.mergeSort (fun a b =>
    let ka := attrSortKey a
    let kb := attrSortKey b
    ka.1 < kb.1 || (ka.1 == kb.1 && ka.2 ≤ kb.2))
  " ".intercalate sorted

/-! ### Instruction printing -/

/-- Implicit information (from the resolved AST) needed to print an instruction. -/
structure InstrHints where
  /-- Alignment to print when the source omits `align` (for `alloca`/`load`/`store`). -/
  defaultAlign? : Option Nat := none

private def joinSp (xs : List String) : String := " ".intercalate (xs.filter (!·.isEmpty))

/-- Find the next top-level comma (or `stop`) from `i`. -/
private def skipToCommaF (fuel : Nat) (c : WCtx) (i stop : Nat) (depth : Nat := 0) : Nat :=
  match fuel with
  | 0 => stop
  | fuel + 1 =>
    if i ≥ stop then stop
    else match c.tok i with
      | .comma => if depth == 0 then i else skipToCommaF fuel c (i + 1) stop depth
      | .lparen | .lbrack | .lbrace | .lpacked | .langle => skipToCommaF fuel c (i + 1) stop (depth + 1)
      | .rparen | .rbrack | .rbrace | .rpacked | .rangle =>
        skipToCommaF fuel c (i + 1) stop (if depth == 0 then 0 else depth - 1)
      | _ => skipToCommaF fuel c (i + 1) stop depth

/-- `skipToCommaF` with the full recursion budget `c.fuel`. -/
private def skipToComma (c : WCtx) (i stop : Nat) (depth : Nat := 0) : Nat :=
  skipToCommaF c.fuel c i stop (depth := depth)

/-- Metadata kind ordering (`LLVMContext` fixed kind IDs) used to sort attachments. -/
def mdKindOrder (nm : String) : Nat :=
  let kinds := ["dbg", "tbaa", "prof", "fpmath", "range", "tbaa.struct", "invariant.load",
    "alias.scope", "noalias", "nontemporal", "llvm.mem.parallel_loop_access", "nonnull",
    "dereferenceable", "dereferenceable_or_null", "make.implicit", "unpredictable",
    "invariant.group", "align", "llvm.loop", "type", "section_prefix", "absolute_symbol",
    "associated", "callees", "irr_loop", "llvm.access.group", "callback",
    "llvm.preserve.access.index", "vcall_visibility", "noundef", "annotation", "nosanitize",
    "func_sanitize", "exclude", "memprof", "callsite", "kcfi_type", "pcsections", "DIAssignID",
    "coro.outside.frame", "mmra", "noalias.addrspace"]
  match kinds.idxOf? nm with
  | some k => k
  | none => 1000

/-- Parse trailing `, !kind !N` attachments from `i` (up to `stop`). -/
def parseAttachmentsF (fuel : Nat) (c : WCtx) (i stop : Nat) (acc : List (String × String) := []) : List (String × String) × Nat :=
  match fuel with
  | 0 => (acc, i)
  | fuel + 1 =>
    if i + 1 < stop && c.tok i == .comma then
      match c.tok (i + 1) with
      | .metaId kind =>
        let (r, j) := mdRefAt c (i + 2)
        parseAttachmentsF fuel c j stop (acc ++ [(kind, r)])
      | _ => (acc, i)
    else (acc, i)

/-- `parseAttachmentsF` with the full recursion budget `c.fuel`. -/
def parseAttachments (c : WCtx) (i stop : Nat) (acc : List (String × String) := []) : List (String × String) × Nat :=
  parseAttachmentsF c.fuel c i stop (acc := acc)

/-- Print sorted metadata attachments (excluding `!dbg`, which LLVM prints last anyway). -/
def printAttachments (atts : List (String × String)) : String :=
  let sorted := atts.mergeSort (fun a b => mdKindOrder a.1 ≤ mdKindOrder b.1)
  String.join (sorted.map fun (k, r) => s!", !{k} {r}")

mutual
/-- Generic operand-list printer: prints `T v` pairs, untyped values (using the last type),
labels, keywords and punctuation until `stop`. -/
def printGenericF (fuel : Nat) (c : WCtx) (i stop : Nat) (cur : PTy) (rawInts : Bool) (acc : String) : String × Nat :=
  match fuel with
  | 0 => (acc, i)
  | fuel + 1 =>
    if i ≥ stop then (acc, i) else
    match c.tok i with
    | .comma =>
      match c.tok (i + 1) with
      | .metaId _ => (acc, i) -- metadata attachments
      | _ => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ ",")
    | .ident "to" =>
      match parseTyAt c (i + 1) with
      | some (t, j) => printGenericF fuel c j stop t rawInts (acc ++ " to " ++ t.print)
      | none => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ " to")
    | .ident "align" =>
      match c.tok (i + 1) with
      | .intLit n => printGenericF fuel c (i + 2) stop cur rawInts (acc ++ s!" align {n}")
      | _ => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ " align")
    | .ident "label" =>
      match c.tok (i + 1) with
      | .localId b => printGenericF fuel c (i + 2) stop cur rawInts (acc ++ " label " ++ c.loc b)
      | _ => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ " label")
    | .lbrack =>
      if (parseTyAt c i).isSome then printTypedF fuel c i stop cur rawInts acc else
      -- phi incoming `[ v, %bb ]`
      match parseValAt c cur (i + 1) with
      | some (v, j) =>
        if c.tok j == .comma then
          match c.tok (j + 1), c.tok (j + 2) with
          | .localId b, .rbrack =>
            printGenericF fuel c (j + 3) stop cur rawInts
              (acc ++ s!" [ {printConst c cur (canon c cur v)}, {c.loc b} ]")
          | _, _ => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ " [")
        else printGenericF fuel c (i + 1) stop cur rawInts (acc ++ " [")
      | none => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ " [")
    | _ => printTypedF fuel c i stop cur rawInts acc

/-- Helper of `printGeneric`: a `T v` pair, a bare type, or an untyped value. -/
def printTypedF (fuel : Nat) (c : WCtx) (i stop : Nat) (cur : PTy) (rawInts : Bool) (acc : String) : String × Nat :=
  match fuel with
  | 0 => (acc, i)
  | fuel + 1 =>
      match parseTyAt c i with
      | some (t, j) =>
        -- `T v` (or a bare type such as `alloca T`)
        let (attrs, j2) := collectAttrs c j
        if startsValue c j2 then
          match parseValAt c t j2 with
          | some (v, k) =>
            printGenericF fuel c k stop t rawInts
              (acc ++ " " ++ joinSp ([t.print] ++ attrs ++ [printConst c t (canon c t v)]))
          | none => printGenericF fuel c j stop t rawInts (acc ++ " " ++ t.print)
        else printGenericF fuel c j2 stop t rawInts (acc ++ " " ++ joinSp ([t.print] ++ attrs))
      | none =>
        if rawInts then
          match c.tok i with
          | .intLit n => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ s!" {n}")
          | _ =>
            match parseValAt c cur i with
            | some (v, k) => printGenericF fuel c k stop cur rawInts (acc ++ " " ++ printConst c cur (canon c cur v))
            | none => printGenericF fuel c (i + 1) stop cur rawInts acc
        else
          match parseValAt c cur i with
          | some (v, k) => printGenericF fuel c k stop cur rawInts (acc ++ " " ++ printConst c cur (canon c cur v))
          | none =>
            match c.tok i with
            | .ident s => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ " " ++ s)
            | .intLit n => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ s!" {n}")
            | .lparen => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ " (")
            | .rparen => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ ")")
            | .rbrack => printGenericF fuel c (i + 1) stop cur rawInts (acc ++ " ]")
            | _ => printGenericF fuel c (i + 1) stop cur rawInts acc
end

/-- Generic operand-list printer (see `printGenericF`). -/
def printGeneric (c : WCtx) (i stop : Nat) (cur : PTy) (rawInts : Bool) (acc : String) :
    String × Nat :=
  printGenericF c.fuel c i stop cur rawInts acc

/-- `Intrinsic::getMangledTypeStr`. -/
def mangleTy (c : WCtx) : PTy → String
  | .int w => s!"i{w}"
  | .byte w => s!"b{w}"
  | .float .half => "f16"
  | .float .bfloat => "bf16"
  | .float .float => "f32"
  | .float .double => "f64"
  | .float .fp128 => "f128"
  | .float .x86_fp80 => "f80"
  | .float .ppc_fp128 => "ppcf128"
  | .ptr as => s!"p{as}"
  | .vec sc n e => (if sc then "nxv" else "v") ++ toString n ++ mangleTy c e
  | .arr n e => s!"a{n}" ++ mangleTy c e
  | .struct _ fs => "sl_" ++ String.join (fs.map (mangleTy c)) ++ "s"
  | .named nm => "s_" ++ nm.toString
  | .void => "isVoid"
  | t => t.print

/-- Overloaded-type positions of intrinsics (`-1` = return type, `k` = argument `k`), used to
re-mangle intrinsic names as LLVM's IR parser does. -/
def intrinsicOverloads : List (String × List Int) :=
  [("llvm.expect.with.probability", [-1]), ("llvm.expect", [-1]),
   ("llvm.experimental.vector.match", [0, 1]),
   ("llvm.experimental.vp.strided.load", [-1, 0, 1]),
   ("llvm.experimental.vp.strided.store", [0, 1, 2]),
   ("llvm.get.active.lane.mask", [-1, 0]),
   ("llvm.mask.beforefirst", [-1]),
   ("llvm.masked.compressstore", [0, 1]), ("llvm.masked.expandload", [-1, 0]),
   ("llvm.masked.gather", [-1, 0]), ("llvm.masked.scatter", [0, 1]),
   ("llvm.masked.load", [-1, 0]), ("llvm.masked.store", [0, 1]),
   ("llvm.matrix.column.major.store", [0, 2]), ("llvm.matrix.column.major.load", [-1, 1]),
   ("llvm.memcpy.inline", [0, 1, 2]), ("llvm.memcpy", [0, 1, 2]), ("llvm.memmove", [0, 1, 2]),
   ("llvm.memset.inline", [0, 2]), ("llvm.memset", [0, 2]),
   ("llvm.scmp", [-1, 0]), ("llvm.ucmp", [-1, 0]),
   ("llvm.speculative.load", [-1, 0]), ("llvm.ssa.copy", [-1]), ("llvm.stepvector", [-1]),
   ("llvm.umin", [-1]), ("llvm.umax", [-1]), ("llvm.smin", [-1]), ("llvm.smax", [-1]),
   ("llvm.vector.interleave2", [-1]), ("llvm.vector.interleave3", [-1]),
   ("llvm.vector.interleave4", [-1]), ("llvm.vector.interleave5", [-1]),
   ("llvm.vector.interleave6", [-1]), ("llvm.vector.interleave7", [-1]),
   ("llvm.vector.interleave8", [-1]),
   ("llvm.vector.deinterleave2", [0]), ("llvm.vector.deinterleave3", [0]),
   ("llvm.vector.deinterleave4", [0]),
   ("llvm.vector.reverse", [-1]),
   ("llvm.vp.gather", [-1, 0]), ("llvm.vp.scatter", [0, 1]), ("llvm.vp.load", [-1, 0]),
   ("llvm.vp.store", [0, 1]), ("llvm.vp.merge", [-1]), ("llvm.vp.select", [-1])]

/-- Re-mangle an intrinsic callee name (`@llvm.vp.load` → `@llvm.vp.load.v4i32.p0`). -/
def remangleIntrinsic (c : WCtx) (callee : String) (ret : PTy) (args : List PTy) : String :=
  if !callee.startsWith "@llvm." then callee else
  let nm := (callee.drop 1).toString
  let cands := intrinsicOverloads.filter fun (base, _) => nm == base || nm.startsWith (base ++ ".")
  -- choose the longest matching base
  match cands.foldl (fun (acc : Option (String × List Int)) cand =>
      match acc with
      | some a => if cand.1.length > a.1.length then some cand else acc
      | none => some cand) none with
  | none => callee
  | some (base, pos) =>
    let tys := pos.map fun k => if k < 0 then ret else args.getD k.toNat .void
    "@" ++ base ++ String.join (tys.map fun t => "." ++ mangleTy c t)

/-- Print the arguments of a call `(...)` starting after `(`; returns text and position after `)`. -/
def printCallArgs (c : WCtx) (i : Nat) (callee : String) : String × List PTy × Nat :=
  let isFPClass := callee.startsWith "@llvm.is.fpclass"
  let rec go (fuel : Nat) (j : Nat) (idx : Nat) (acc : List String) (tys : List PTy) : List String × List PTy × Nat :=
    match fuel with
    | 0 => (acc, tys, j)
    | fuel + 1 =>
      if c.tok j == .rparen then (acc, tys, j + 1)
      else if c.tok j == .eof then (acc, tys, j)
      else
        match parseTyAt c j with
        | some (t, k) =>
          let (attrs, k2) := collectAttrs c k
          match parseValAt c t k2 with
          | some (v, l) =>
            let cv := canon c t v
            let comment :=
              if isFPClass && idx == 1 then
                match cv with
                | CVal.int m => s!"/* {fpClassTestString m.toNat} */ "
                | _ => ""
              else ""
            let item := comment ++ joinSp ([t.print] ++ attrs ++ [printConst c t cv])
            let next := if c.tok l == .comma then l + 1 else l
            go fuel next (idx + 1) (acc ++ [item]) (tys ++ [t])
          | none => (acc, tys, k2)
        | none => (acc, tys, j + 1)
  let (items, tys, j) := go c.fuel i 0 [] []
  (", ".intercalate items, tys, j)

/-- Print operand bundles `[ "tag"(T v, ...), ... ]` starting at `[`. -/
def printBundles (c : WCtx) (i : Nat) : String × Nat :=
  let rec goBundle (fuel : Nat) (j : Nat) (acc : List String) : List String × Nat :=
    match fuel with
    | 0 => (acc, j)
    | fuel + 1 =>
      match c.tok j with
      | .strLit tag =>
        if c.tok (j + 1) == .lparen then
          let rec goOps (fuel : Nat) (k : Nat) (ops : List String) : List String × Nat :=
            match fuel with
            | 0 => (ops, k)
            | fuel + 1 =>
              if c.tok k == .rparen then (ops, k + 1)
              else
                match parseTyAt c k with
                | some (t, l) =>
                  match parseValAt c t l with
                  | some (v, m) =>
                    let next := if c.tok m == .comma then m + 1 else m
                    goOps fuel next (ops ++ [printTypedOperand c t v])
                  | none => (ops, l)
                | none => (ops, k + 1)
          let (ops, k) := goOps c.fuel (j + 2) []
          let b := s!"\"{tag}\"({", ".intercalate ops})"
          if c.tok k == .comma then goBundle fuel (k + 1) (acc ++ [b]) else (acc ++ [b], k)
        else (acc, j + 1)
      | _ => (acc, j)
  let (bs, j) := goBundle c.fuel (i + 1) []
  let j' := if c.tok j == .rbrack then j + 1 else j
  (s!"[ {", ".intercalate bs} ]", j')

/-- Print a `call` (after an optional `%x = ` prefix) from token `i`. -/
def printCall (c : WCtx) (i stop : Nat) : String :=
  -- prefix keywords: tail markers, `call`, FMF, calling convention, return attributes
  let rec pre (fuel : Nat) (j : Nat) (acc : List String) : List String × Nat :=
    match fuel with
    | 0 => (acc, j)
    | fuel + 1 =>
      match c.tok j with
      | .ident s =>
        if s ∈ ["tail", "musttail", "notail", "call", "invoke", "callbr"] then pre fuel (j + 1) (acc ++ [s])
        else if flagWords.contains s then
          let (fs, k) := collectFlags c j
          pre fuel k (acc ++ canonFlags fs)
        else if s.endsWith "cc" && !(parseTyAt c j).isSome then pre fuel (j + 1) (acc ++ [s])
        else if s == "cc" then
          match c.tok (j + 1) with
          | .intLit n => pre fuel (j + 2) (acc ++ [s!"cc {n}"])
          | _ => pre fuel (j + 1) (acc ++ [s])
        else (acc, j)
      | _ => (acc, j)
  let (preWords, j0) := pre c.fuel i []
  let (retAttrs, j1) := collectAttrs c j0
  match parseTyAt c j1 with
  | none => joinSp preWords
  | some (retTy, j2) =>
    -- optional explicit function type
    let (fnTy?, j3) : Option PTy × Nat :=
      if c.tok j2 == .lparen then
        let rec goP (fuel : Nat) (k : Nat) (ps : List PTy) : List PTy × Bool × Nat :=
          match fuel with
          | 0 => (ps, false, k)
          | fuel + 1 =>
            match c.tok k with
            | .rparen => (ps, false, k + 1)
            | .ellipsis => (ps, true, if c.tok (k + 1) == .rparen then k + 2 else k + 1)
            | .comma => goP fuel (k + 1) ps
            | _ =>
              match parseTyAt c k with
              | some (t, l) => goP fuel l (ps ++ [t])
              | none => (ps, false, k + 1)
        let (ps, va, k) := goP c.fuel (j2 + 1) []
        (some (.fn retTy ps va), k)
      else (none, j2)
    let (calleeStr, j4) :=
      if c.tok j3 == .ident "asm" then
        -- inline asm: `asm [sideeffect] [alignstack] [inteldialect] [unwind] "code", "constraints"`
        let rec goAsm (fuel : Nat) (k : Nat) (acc : List String) : List String × Nat :=
          match fuel with
          | 0 => (acc, k)
          | fuel + 1 =>
            match c.tok k with
            | .ident w => if w ∈ ["sideeffect", "alignstack", "inteldialect", "unwind"] then goAsm fuel (k + 1) (acc ++ [w]) else (acc, k)
            | _ => (acc, k)
        let (flags, k1) := goAsm c.fuel (j3 + 1) []
        match c.tok k1, c.tok (k1 + 1), c.tok (k1 + 2) with
        | .strLit code, .comma, .strLit cons =>
          (joinSp (["asm"] ++ flags ++ [s!"\"{code}\", \"{cons}\""]), k1 + 3)
        | _, _, _ => ("asm", k1)
      else
      match parseValAt c (.ptr 0) j3 with
      | some (v, k) => (printConst c (.ptr 0) v, k)
      | none => ("", j3 + 1)
    let declVarArg := match c.fnTypes.find? (fun (n, _) => "@" ++ n == calleeStr ||
        printLLVMName "@" n == calleeStr) with
      | some (_, .function _ _ va) => va
      | _ => false
    let tyStr := match fnTy? with
      | some ft@(.fn _ _ true) => ft.print
      | some ft@(.fn _ _ _) => if calleeStr.startsWith "asm" then ft.print else retTy.print
      | _ => if declVarArg then
               match c.fnTypes.find? (fun (n, _) => printLLVMName "@" n == calleeStr) with
               | some (_, t) => (PTy.ofLlvmType t).print
               | none => retTy.print
             else retTy.print
    let (argStr, argTys, j5) :=
      if c.tok j4 == .lparen then printCallArgs c (j4 + 1) calleeStr else ("", [], j4)
    let calleeStr := remangleIntrinsic c calleeStr retTy argTys
    let (fnAttrs0, j6) := collectAttrs c j5
    -- call-site function attributes print as an attribute group `#N`, numbered by the slot
    -- tracker; mark them with their canonical key, resolved to a number by the caller
    let fnAttrs := if fnAttrs0.isEmpty then [] else ["#⟦" ++ attrSetKey c fnAttrs0 ++ "⟧"]
    let (bundleStr, j7) := if c.tok j6 == .lbrack then printBundles c j6 else ("", j6)
    let (atts, _) := parseAttachments c j7 stop
    joinSp (preWords ++ retAttrs ++ [tyStr, s!"{calleeStr}({argStr})"] ++ fnAttrs ++ [bundleStr])
      ++ printAttachments atts

/-- Print the instruction whose tokens are `[start, stop)` (LLVM `Instruction::print` text,
including the two-space indentation). -/
def printInstruction (c0 : WCtx) (start stop : Nat) (hints : InstrHints := {})
    (iid? : Option InstructionId := none) : String :=
  let c := { c0 with limit := stop }
  let (namePrefix, i0) : String × Nat :=
    match c.tok start, c.tok (start + 1) with
    | .localId id, .eq => (c.loc id ++ " = ", start + 2)
    | _, _ =>
      match iid? with
      | some (.id rid) => (c.loc rid ++ " = ", start)
      | _ => ("", start)
  let body : String :=
    match c.tok i0 with
    | .ident op =>
      if op ∈ ["call", "tail", "musttail", "notail"] then printCall c i0 stop
      else if op == "callbr" then
        -- `callbr T callee(args) to label %d [label %a, ...]`
        let rec findToCb (fuel : Nat) (k : Nat) : Nat :=
          match fuel with
          | 0 => stop
          | fuel + 1 =>
            if k ≥ stop then stop else if c.tok k == .ident "to" then k else findToCb fuel (k + 1)
        let toPos := findToCb c.fuel i0
        let callText := printCall { c with limit := toPos } i0 toPos
        let dflt := match c.tok (toPos + 1), c.tok (toPos + 2) with
          | .ident "label", .localId b => c.loc b
          | _, _ => ""
        let rec labelsCb (fuel : Nat) (m : Nat) (acc : List String) : List String :=
          match fuel with
          | 0 => acc
          | fuel + 1 =>
            match c.tok m, c.tok (m + 1) with
            | .ident "label", .localId b =>
              let acc' := acc ++ [s!"label {c.loc b}"]
              if c.tok (m + 2) == .comma then labelsCb fuel (m + 3) acc' else acc'
            | _, _ => acc
        let ind := labelsCb c.fuel (toPos + 4) []
        callText ++ "\n          to label " ++ dflt ++ " [" ++ ", ".intercalate ind ++ "]"
      else if op == "invoke" then
        -- `invoke T callee(args) to label %n unwind label %u`
        let rec findTo (fuel : Nat) (k : Nat) : Nat :=
          match fuel with
          | 0 => stop
          | fuel + 1 =>
            if k ≥ stop then stop else if c.tok k == .ident "to" then k else findTo fuel (k + 1)
        let toPos := findTo c.fuel i0
        let callText := printCall { c with limit := toPos } i0 toPos
        let callText := if callText.startsWith "invoke" then callText else callText
        let (rest, _) := printGeneric c toPos stop .void false ""
        callText ++ "\n         " ++ rest
      else if op == "switch" then
        -- switch T v, label %d [ T v, label %x ... ]
        match parseTyAt c (i0 + 1) with
        | some (t, j) =>
          match parseValAt c t j with
          | some (v, k) =>
            let (dflt, k2) : String × Nat :=
              match c.tok (k + 1), c.tok (k + 2) with
              | .ident "label", .localId b => (c.loc b, k + 3)
              | _, _ => ("", k + 1)
            let rec cases (fuel : Nat) (m : Nat) (acc : List String) : List String :=
              match fuel with
              | 0 => acc
              | fuel + 1 =>
                match parseTyAt c m with
                | some (ct, m1) =>
                  match parseValAt c ct m1 with
                  | some (cv, m2) =>
                    match c.tok (m2 + 1), c.tok (m2 + 2) with
                    | .ident "label", .localId b =>
                      cases fuel (m2 + 3) (acc ++ [s!"    {printTypedOperand c ct cv}, label {c.loc b}\n"])
                    | _, _ => acc
                  | none => acc
                | none => acc
            let cs := cases c.fuel (k2 + 1) []
            s!"switch {printTypedOperand c t v}, label {dflt} [\n" ++ String.join cs ++ "  ]"
          | none => "switch"
        | none => "switch"
      else if op == "indirectbr" then
        match parseTyAt c (i0 + 1) with
        | some (t, j) =>
          match parseValAt c t j with
          | some (v, k) =>
            let rec labels (fuel : Nat) (m : Nat) (acc : List String) : List String :=
              match fuel with
              | 0 => acc
              | fuel + 1 =>
                match c.tok m, c.tok (m + 1) with
                | .ident "label", .localId b =>
                  let acc' := acc ++ [s!"label {c.loc b}"]
                  if c.tok (m + 2) == .comma then labels fuel (m + 3) acc' else acc'
                | _, _ => acc
            s!"indirectbr {printTypedOperand c t v}, [{", ".intercalate (labels c.fuel (k + 2) [])}]"
          | none => "indirectbr"
        | none => "indirectbr"
      else if op == "shufflevector" then
        -- two typed vector operands then the mask (printed via `printShuffleMask`)
        let (s1, j1) := printGeneric c (i0 + 1) (skipToComma c (i0 + 1) stop) .void false ""
        let j1' := j1 + 1
        let e2 := skipToComma c j1' stop
        let (s2, _) := printGeneric c j1' e2 .void false ""
        let maskStr :=
          match parseTyAt c (e2 + 1) with
          | some (mt, k) =>
            match parseValAt c mt k with
            | some (mv, _) =>
              let elems : List (Option Int) := match mv with
                | .agg es => es.map fun (p : PTy × CVal) => match p.2 with | CVal.int n => some n | _ => none
                | .zero => List.replicate (match mt with | .vec _ n _ => n | _ => 0) (some 0)
                | .poison | .undef => List.replicate (match mt with | .vec _ n _ => n | _ => 0) none
                | .splat _ (CVal.int n) => List.replicate (match mt with | .vec _ n _ => n | _ => 0) (some n)
                | _ => []
              let body :=
                if elems.all (· == some 0) then "zeroinitializer"
                else if elems.all (·.isNone) then "poison"
                else "<" ++ ", ".intercalate (elems.map fun (o : Option Int) => match o with
                  | some n => s!"i32 {n}" | _ => "i32 poison") ++ ">"
              s!"{mt.print} {body}"
            | none => ""
          | none => ""
        s!"shufflevector{s1},{s2}, {maskStr}"
      else
        let (flags, j) := collectFlags c (i0 + 1)
        let isVol := c.tok j == .ident "volatile"
        let j' := if isVol then j + 1 else j
        let opWords := [op] ++ canonFlags flags ++ (if isVol then ["volatile"] else [])
        let rawInts := op == "extractvalue" || op == "insertvalue"
        -- operands end at metadata attachments
        let rec findAttach (fuel : Nat) (k : Nat) : Nat :=
          match fuel with
          | 0 => stop
          | fuel + 1 =>
            if k ≥ stop then stop
            else if c.tok k == .comma && (match c.tok (k + 1) with | .metaId _ => true | _ => false)
              then k else findAttach fuel (k + 1)
        let opEnd := findAttach c.fuel j'
        -- predicates for icmp/fcmp
        let (predWords, j2) : List String × Nat :=
          if op == "icmp" || op == "fcmp" then
            match c.tok j' with
            | .ident p => ([p], j' + 1)
            | _ => ([], j')
          else ([], j')
        let (operands0, _) := printGeneric c j2 opEnd .void rawInts ""
        -- `alloca T, i32 1` prints as `alloca T`
        let operands :=
          if op == "alloca" then
            match operands0.splitOn ", i32 1" with
            | [a, b] => if b.isEmpty || b.startsWith "," then a ++ b else operands0
            | _ => operands0
          else operands0
        let hasAlign := (List.range (opEnd - j2)).any fun d => c.tok (j2 + d) == .ident "align"
        let alignStr :=
          if !hasAlign && (op == "load" || op == "store" || op == "alloca") then
            match hints.defaultAlign? with
            | some a => s!", align {a}"
            | none => ""
          else ""
        -- `alloca` prints `addrspace(N)` after `align`; reorder if needed
        let operands' :=
          if op == "alloca" && alignStr != "" then
            match operands.splitOn ", addrspace" with
            | [a, b] => a ++ alignStr ++ ", addrspace" ++ b
            | _ => operands ++ alignStr
          else operands ++ alignStr
        let (atts, _) := parseAttachments c opEnd stop
        joinSp (opWords ++ predWords) ++ operands' ++ printAttachments atts
    | _ => "<unknown>"
  "  " ++ namePrefix ++ body

/-- Print the formal parameters of a function definition as LLVM's `Argument::print` would. -/
def printParams (c0 : WCtx) (start stop : Nat) : List String :=
  let c := { c0 with limit := stop }
  let rec go (fuel : Nat) (j : Nat) (acc : List String) (anon : Nat) : List String :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if j ≥ stop then acc
      else if c.tok j == .ellipsis then acc
      else
        match parseTyAt c j with
        | some (t, k) =>
          let (attrs, k2) := collectAttrs c k
          let (nm, k3, anon') := match c.tok k2 with
            | .localId id => (c.loc id, k2 + 1, anon)
            | _ => (s!"%{anon}", k2, anon + 1)
          let _ := attrs
          let item := joinSp [t.print, nm]
          let next := if c.tok k3 == .comma then k3 + 1 else k3
          go fuel next (acc ++ [item]) anon'
        | none => acc
  go c.fuel start [] 0

end LeanNanoLlvm.Llubi
