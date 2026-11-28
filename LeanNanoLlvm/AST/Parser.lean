import LeanNanoLlvm.AST.Lexer
import LeanNanoLlvm.AST.Resolve
import LeanNanoLlvm.AST.DataLayout

/-!
# Standalone `.ll` Text Parser

A pure-Lean, total (fuel-bounded) lexer and recursive-descent parser for LLVM IR
text (`.ll`) files into `LeanNanoLlvm.AST.TopLevel` and `DataLayout`.

Supports:
- `;` line comments, `target datalayout = "..."`, `target triple = "..."`,
  `source_filename = "..."`, `attributes #N = { ... }`, and metadata nodes `!N = !{...}`
- Named struct definitions `%T = type { ... }` / `%T = type <{ ... }>`
- Globals (`global` / `constant`, linkage, `addrspace(N)`, initializers, `align N`)
- Declarations & definitions (linkage, calling conventions, parameter/return attributes
  including `noundef`, `nonnull`, `align`, `dereferenceable`, `dereferenceable_or_null`,
  `range`, `byval`, `sret`, `noalias`, `readonly`, implicit entry labels, anonymous SSA IDs)
- All integer, FP, comparison, cast, `select`, `phi`, `freeze`, memory (`alloca`, `load`
  with `!noundef`/`!nonnull`/`!range`, `store`, `getelementptr`), aggregate, vector, `call`,
  and terminator (`ret`, `br`, `switch`, `unreachable`) instructions.
-/

namespace LeanNanoLlvm.AST.Parser

/-! ### `target datalayout` strings -/

/-- Parse an LLVM `target datalayout = "..."` string into `DataLayout`. -/
def parseDataLayoutString (s : String) : DataLayout :=
  let parts := s.splitOn "-"
  parts.foldl (init := DataLayout.default64LE) fun dl part =>
    if part == "e" then { dl with endianness := .little }
    else if part == "E" then { dl with endianness := .big }
    else if part.startsWith "p" then
      -- `p[<flags>][<as>][(<name>)]:...` (LangRef "Data Layout"): flags are `u` (unstable
      -- representation), `e` (external state), `z` (all-zeros null), `o` (all-ones null).
      let afterP := (part.drop 1).toString
      let flags := afterP.takeWhile (fun c => c == 'u' || c == 'e' || c == 'z' || c == 'o')
      let allOnesNull := flags.contains 'o'
      let restStr := (afterP.drop flags.length).toString
      -- drop an optional address-space name `(name)` before the first `:`
      let restStr := match restStr.splitOn ":" with
        | asPart :: more => ":".intercalate ((asPart.takeWhile (· != '(')).toString :: more)
        | [] => restStr
      let fields := restStr.splitOn ":"
      match fields with
      | asStr :: sizeStr :: abiStr :: rest =>
        let asNum := if asStr.isEmpty then 0 else (parseNatStr asStr).getD 0
        let sizeBits := (parseNatStr sizeStr).getD 64
        let abiBytes := ((parseNatStr abiStr).getD 64) / 8
        let (prefBytes, idxBits) :=
          match rest with
          | [] => (abiBytes, sizeBits)
          | [prefStr] => (((parseNatStr prefStr).getD (abiBytes * 8)) / 8, sizeBits)
          | prefStr :: idxStr :: _ =>
            (((parseNatStr prefStr).getD (abiBytes * 8)) / 8, (parseNatStr idxStr).getD sizeBits)
        let pl : PointerLayout := {
          addrSpace := asNum
          sizeBits := sizeBits
          abiAlign := if abiBytes == 0 then 1 else abiBytes
          prefAlign := if prefBytes == 0 then 1 else prefBytes
          indexBits := idxBits
          nullAddr := if allOnesNull then (1 <<< sizeBits) - 1 else 0
        }
        if asNum == 0 then { dl with defaultPtr := pl }
        else { dl with addrSpacePtrs := pl :: dl.addrSpacePtrs }
      | _ => dl
    else if part.startsWith "i" then
      let fields := (part.drop 1).toString.splitOn ":"
      match fields with
      | wStr :: abiStr :: rest =>
        match parseNatStr wStr, parseNatStr abiStr with
        | some w, some abiBits =>
          let abiBytes := max 1 (abiBits / 8)
          let prefBytes := match rest with
            | prefStr :: _ => match parseNatStr prefStr with
              | some pb => max 1 (pb / 8)
              | none => abiBytes
            | [] => abiBytes
          { dl with intAligns := (w, abiBytes) :: dl.intAligns,
                    intPrefAligns := (w, prefBytes) :: dl.intPrefAligns }
        | _, _ => dl
      | _ => dl
    else if part.startsWith "P" then
      match parseNatStr (part.drop 1).toString with
      | some n => { dl with programAddrSpace := n }
      | none => dl
    else if part.startsWith "A" then
      match parseNatStr (part.drop 1).toString with
      | some n => { dl with allocaAddrSpace := n }
      | none => dl
    else if part.startsWith "G" then
      match parseNatStr (part.drop 1).toString with
      | some n => { dl with globalsAddrSpace := n }
      | none => dl
    else dl

/-! ### Parser state and token primitives -/

/-- Source location of one parsed instruction / terminator: its token range and 0-based line. -/
structure SrcEntry where
  iid      : InstructionId
  startTok : Nat
  endTok   : Nat
  line     : Nat
deriving Repr, Inhabited

/-- Source information for one function definition (used by printers needing the exact source). -/
structure FnSrc where
  name        : FunctionId
  /-- Token range of the parameter list (between, and excluding, the parentheses). -/
  paramsStart : Nat
  paramsEnd   : Nat
  entries     : Array SrcEntry
deriving Repr, Inhabited

/-- Parser state holding token stream, cursor, metadata tables, and void/anon counters. -/
structure PState where
  toks         : Array Tok
  pos          : Nat := 0
  nextVoid     : Nat := 0
  nextAnon     : Nat := 0
  rangeMeta    : List (String × List (Int × Int)) := []
  intMeta      : List (String × Nat) := []
  noReturnGrps : List Nat := []
  /-- `denormal_fpenv` of attribute groups: group, general mode, `float:` mode. -/
  denormGrps   : List (Nat × Option DenormalMode × Option DenormalMode) := []
  vscale       : Nat := 4
  /-- Named type definitions seen so far, as `(name, type, type at vscale = 1)`, used only to
  compute LLVM's recorded alignment for memory operations on scalable types. -/
  typeDefs     : List (LocalId × LlvmType × LlvmType) := []
  curSrc       : Array SrcEntry := #[]
  lines        : Array Nat := #[]
  fnSrcs       : Array FnSrc := #[]
  /-- The last floating-point type parsed: the type of an `f0x` literal that follows it (its bit
  pattern's word order depends on the type, see `decodeHexFloatForType`). -/
  lastFloatTy  : Option FloatType := none
deriving Inhabited

abbrev ParseM := StateT PState (Except String)

private def peek : ParseM Tok := do
  let st ← get
  return st.toks.getD st.pos .eof

private def peekAt (offset : Nat) : ParseM Tok := do
  let st ← get
  return st.toks.getD (st.pos + offset) .eof

private def bump : ParseM Tok := do
  let st ← get
  let t := st.toks.getD st.pos .eof
  set { st with pos := st.pos + 1 }
  return t

private def expect (tok : Tok) (ctx : String) : ParseM Unit := do
  let t ← bump
  if t == tok then return ()
  else throw s!"parse error ({ctx}): expected {repr tok}, got {repr t}"

private def expectIdent (s : String) (ctx : String) : ParseM Unit := do
  let t ← bump
  if t == .ident s then return ()
  else throw s!"parse error ({ctx}): expected '{s}', got {repr t}"

private def tryEat (tok : Tok) : ParseM Bool := do
  let t ← peek
  if t == tok then let _ ← bump; return true
  else return false

private def tryEatIdent (s : String) : ParseM Bool := do
  let t ← peek
  if t == .ident s then let _ ← bump; return true
  else return false

private def freshVoidId : ParseM InstructionId := do
  let st ← get
  set { st with nextVoid := st.nextVoid + 1 }
  return .void st.nextVoid

private def freshAnonId : ParseM RawId := do
  let st ← get
  set { st with nextAnon := st.nextAnon + 1 }
  return .anonymous st.nextAnon

private def parseNatTok (ctx : String) : ParseM Nat := do
  match ← bump with
  | .intLit n =>
    if n ≥ 0 then return n.toNat
    else throw s!"parse error ({ctx}): expected non-negative integer, got {n}"
  | t => throw s!"parse error ({ctx}): expected integer, got {repr t}"

private def parseIntTok (ctx : String) : ParseM Int := do
  match ← bump with
  | .intLit n => return n
  | t => throw s!"parse error ({ctx}): expected integer, got {repr t}"

private def parseRawLocalId (ctx : String) : ParseM RawId := do
  match ← bump with
  | .localId id => return id
  | t => throw s!"parse error ({ctx}): expected %id, got {repr t}"

private def parseRawGlobalId (ctx : String) : ParseM RawId := do
  match ← bump with
  | .globalId id => return id
  | t => throw s!"parse error ({ctx}): expected @id, got {repr t}"

/-! ### Types, flags and attributes -/

/-- Parse an LLVM type (total on `fuel`). -/
def parseType : Nat → ParseM LlvmType
  | 0 => throw "parse error: recursion limit exceeded in parseType"
  | fuel + 1 => do
    let t ← bump
    match t with
    | .ident "half" => modify fun st => { st with lastFloatTy := some .half }; return .float .half
    | .ident "bfloat" => modify fun st => { st with lastFloatTy := some .bfloat }; return .float .bfloat
    | .ident "float" => modify fun st => { st with lastFloatTy := some .float }; return .float .float
    | .ident "double" => modify fun st => { st with lastFloatTy := some .double }; return .float .double
    | .ident "x86_fp80" =>
      modify fun st => { st with lastFloatTy := some .x86_fp80 }; return .float .x86_fp80
    | .ident "fp128" => modify fun st => { st with lastFloatTy := some .fp128 }; return .float .fp128
    | .ident "ppc_fp128" =>
      modify fun st => { st with lastFloatTy := some .ppc_fp128 }; return .float .ppc_fp128
    | .ident "metadata" => return .ptr 0
    | .ident "ptr" =>
      if ← tryEatIdent "addrspace" then
        expect .lparen "ptr addrspace"
        let as ← parseNatTok "ptr addrspace"
        expect .rparen "ptr addrspace"
        return .ptr as
      else
        return .ptr 0
    | .ident s =>
      if s.startsWith "i" then
        match parseNatStr (s.drop 1).toString with
        | some w => return .int w
        | none => throw s!"parse error: unknown type '{s}'"
      else if s.startsWith "b" then
        match parseNatStr (s.drop 1).toString with
        | some w => return .byte w
        | none => throw s!"parse error: unknown type '{s}'"
      else
        throw s!"parse error: unknown type '{s}'"
    | .localId id => return .named id
    | .langle =>
      -- Vector `<N x T>`, `<Nx T>`, or `<vscale x N x T>`
      let isScalable ← tryEatIdent "vscale"
      if isScalable then
        let _ ← tryEatIdent "x"
      let n ←
        match ← bump with
        | .intLit k =>
          if k ≥ 0 then
            let _ ← tryEatIdent "x"
            pure k.toNat
          else throw s!"parse error: negative vector length {k}"
        | .ident nx =>
          if nx.endsWith "x" then
            match parseNatStr (nx.dropEnd 1).toString with
            | some k => pure k
            | none => throw s!"parse error: bad vector length '{nx}'"
          else throw s!"parse error: expected vector length, got '{nx}'"
        | tok => throw s!"parse error: expected vector length, got {repr tok}"
      let elem ← parseType fuel
      expect .rangle "vector type"
      let vscale := (← get).vscale
      return .vector (if isScalable then n * vscale else n) elem
    | .lbrack =>
      -- Array `[N x T]`
      let n ← parseNatTok "array length"
      expectIdent "x" "array type"
      let elem ← parseType fuel
      expect .rbrack "array type"
      return .array n elem
    | .lbrace =>
      -- Non-packed struct `{ T1, T2, ... }`
      let mut fields : List LlvmType := []
      if !(← tryEat .rbrace) then
        let mut go := true
        let mut guard := fuel
        while go && guard > 0 do
          guard := guard - 1
          let ft ← parseType fuel
          fields := ft :: fields
          if ← tryEat .comma then go := true
          else
            expect .rbrace "struct type"
            go := false
      return .struct false fields.reverse
    | .lpacked =>
      -- Packed struct `<{ T1, T2, ... }>`
      let mut fields : List LlvmType := []
      if !(← tryEat .rpacked) then
        let mut go := true
        let mut guard := fuel
        while go && guard > 0 do
          guard := guard - 1
          let ft ← parseType fuel
          fields := ft :: fields
          if ← tryEat .comma then go := true
          else
            expect .rpacked "packed struct type"
            go := false
      return .struct true fields.reverse
    | tok => throw s!"parse error: unexpected token {repr tok} in type"

def parseRetType (fuel : Nat) : ParseM LlvmRetType := do
  if ← tryEatIdent "void" then return .void
  else return .ret (← parseType fuel)

/-- Parse optional FastMathFlags (`nnan`, `ninf`, `nsz`, `arcp`, `contract`, `afn`, `reassoc`, `fast`). -/
def parseFMF : ParseM FastMathFlags := do
  let mut fmf : FastMathFlags := {}
  let mut cont := true
  let mut guard := 16
  while cont && guard > 0 do
    guard := guard - 1
    match ← peek with
    | .ident "nnan" => let _ ← bump; fmf := { fmf with nnan := true }
    | .ident "ninf" => let _ ← bump; fmf := { fmf with ninf := true }
    | .ident "nsz" => let _ ← bump; fmf := { fmf with nsz := true }
    | .ident "arcp" => let _ ← bump; fmf := { fmf with arcp := true }
    | .ident "contract" => let _ ← bump; fmf := { fmf with contract := true }
    | .ident "afn" => let _ ← bump; fmf := { fmf with afn := true }
    | .ident "reassoc" => let _ ← bump; fmf := { fmf with reassoc := true }
    | .ident "fast" => let _ ← bump; fmf := FastMathFlags.fast
    | _ => cont := false
  return fmf

/-- Skip balanced parenthesized group `(...)` if next token is `(`. -/
private def skipParenGroup (fuel : Nat) : ParseM Unit := do
  if !(← tryEat .lparen) then return ()
  let mut depth : Nat := 1
  let mut guard := fuel
  while depth > 0 && guard > 0 do
    guard := guard - 1
    match ← bump with
    | .lparen => depth := depth + 1
    | .rparen => depth := depth - 1
    | .eof => depth := 0
    | _ => pure ()

/-- Parse a list of LLVM parameter/return value attributes. Unknown attributes are safely ignored. -/
def parseValueAttrs (fuel : Nat) : ParseM (List ValueAttr) := do
  let mut attrs : List ValueAttr := []
  let mut cont := true
  let mut guard := 32
  while cont && guard > 0 do
    guard := guard - 1
    match ← peek with
    | .ident "noundef" => let _ ← bump; attrs := .noundef :: attrs
    | .ident "nonnull" => let _ ← bump; attrs := .nonnull :: attrs
    | .ident "noalias" => let _ ← bump; attrs := .noalias :: attrs
    | .ident "readonly" => let _ ← bump; attrs := .readonly :: attrs
    | .ident "align" =>
      let _ ← bump
      if ← tryEat .lparen then
        let a ← parseNatTok "align(N)"
        expect .rparen "align(N)"
        attrs := .align a :: attrs
      else
        let a ← parseNatTok "align N"
        attrs := .align a :: attrs
    | .ident "dereferenceable" =>
      let _ ← bump
      expect .lparen "dereferenceable"
      let n ← parseNatTok "dereferenceable"
      expect .rparen "dereferenceable"
      attrs := .dereferenceable n :: attrs
    | .ident "dereferenceable_or_null" =>
      let _ ← bump
      expect .lparen "dereferenceable_or_null"
      let n ← parseNatTok "dereferenceable_or_null"
      expect .rparen "dereferenceable_or_null"
      attrs := .dereferenceableOrNull n :: attrs
    | .ident "range" =>
      let _ ← bump
      expect .lparen "range"
      -- LLVM syntax: `range(i32 lo, hi)` or `range(lo, hi)`
      let t0 ← peek
      match t0 with
      | .ident _ => let _ ← parseType fuel
      | _ => pure ()
      let lo ← parseIntTok "range lo"
      expect .comma "range"
      let hi ← parseIntTok "range hi"
      expect .rparen "range"
      attrs := .range lo hi :: attrs
    | .ident "byval" =>
      let _ ← bump
      expect .lparen "byval"
      let ty ← parseType fuel
      expect .rparen "byval"
      attrs := .byval ty :: attrs
    | .ident "sret" =>
      let _ ← bump
      expect .lparen "sret"
      let ty ← parseType fuel
      expect .rparen "sret"
      attrs := .sret ty :: attrs
    | .ident "nofpclass" =>
      let _ ← bump
      if ← tryEat .lparen then
        let mut mask : Nat := 0
        let mut g := 32
        while !(← tryEat .rparen) && g > 0 do
          g := g - 1
          match ← bump with
          | .ident "snan" => mask := mask ||| 1
          | .ident "qnan" => mask := mask ||| 2
          | .ident "nan" => mask := mask ||| 3
          | .ident "ninf" => mask := mask ||| 4
          | .ident "nnorm" => mask := mask ||| 8
          | .ident "nsub" => mask := mask ||| 16
          | .ident "nzero" => mask := mask ||| 32
          | .ident "pzero" => mask := mask ||| 64
          | .ident "psub" => mask := mask ||| 128
          | .ident "pnorm" => mask := mask ||| 256
          | .ident "pinf" => mask := mask ||| 512
          | .ident "inf" => mask := mask ||| 516
          | .ident "norm" => mask := mask ||| 264
          | .ident "sub" => mask := mask ||| 144
          | .ident "zero" => mask := mask ||| 96
          | .ident "all" => mask := mask ||| 1023
          | .intLit n => mask := mask ||| n.toNat
          | .eof => g := 0
          | _ => pure ()
        attrs := .nofpclass mask :: attrs
    -- Common LLVM attributes that do not change value semantics here
    | .ident "signext" | .ident "zeroext" | .ident "inreg" | .ident "nocapture"
    | .ident "nofree" | .ident "writeonly" | .ident "readnone" | .ident "returned"
    | .ident "immarg" | .ident "dead_on_unwind" | .ident "writable" | .ident "nest"
    | .ident "swiftself" | .ident "swifterror" | .ident "inalloca" | .ident "preallocated"
    | .ident "captures" | .ident "dead_on_return" | .ident "initializes" =>
      let _ ← bump
      skipParenGroup fuel
    | _ => cont := false
  return attrs.reverse

private def parseGEPFlags : ParseM GEPFlags := do
  let mut flags : GEPFlags := {}
  let mut cont := true
  let mut guard := 8
  while cont && guard > 0 do
    guard := guard - 1
    match ← peek with
    | .ident "inbounds" => let _ ← bump; flags := { flags with inbounds := true, nusw := true }
    | .ident "nusw" => let _ ← bump; flags := { flags with nusw := true }
    | .ident "nuw" => let _ ← bump; flags := { flags with nuw := true }
    | _ => cont := false
  return flags

private def parseICmpPred (ctx : String) : ParseM ICmpPred := do
  match ← bump with
  | .ident "eq" => return .eq
  | .ident "ne" => return .ne
  | .ident "ugt" => return .ugt
  | .ident "uge" => return .uge
  | .ident "ult" => return .ult
  | .ident "ule" => return .ule
  | .ident "sgt" => return .sgt
  | .ident "sge" => return .sge
  | .ident "slt" => return .slt
  | .ident "sle" => return .sle
  | t => throw s!"parse error ({ctx}): expected icmp predicate, got {repr t}"

private def parseFCmpPred (ctx : String) : ParseM FCmpPred := do
  match ← bump with
  | .ident "false" => return .ffalse
  | .ident "oeq" => return .oeq
  | .ident "ogt" => return .ogt
  | .ident "oge" => return .oge
  | .ident "olt" => return .olt
  | .ident "ole" => return .ole
  | .ident "one" => return .one
  | .ident "ord" => return .ord
  | .ident "ueq" => return .ueq
  | .ident "ugt" => return .ugt
  | .ident "uge" => return .uge
  | .ident "ult" => return .ult
  | .ident "ule" => return .ule
  | .ident "une" => return .une
  | .ident "uno" => return .uno
  | .ident "true" => return .ftrue
  | t => throw s!"parse error ({ctx}): expected fcmp predicate, got {repr t}"

/-! ### Operands and constants -/

/-- Convert an LLVM 64-bit hex float literal (`0x...`) to bit representation for `ty` if needed. -/
private def decodeHexFloatForType (tag : Char) (val : Nat) : Exp :=
  if tag == 'L' then
    -- LLVM `0xL<lo64><hi64>` writes the low 64-bit word before the high 64-bit word
    let mask64 : Nat := (1 <<< 64) - 1
    let lo64 := val >>> 64
    let hi64 := val &&& mask64
    .floatBits ((hi64 <<< 64) ||| lo64)
  else if tag == 'K' then
    -- LLVM `0xK<80-bit>`: the x87 encoding itself (sign, 15-bit exponent, explicit integer bit,
    -- 63-bit fraction), which is also our `x86_fp80` representation (`FloatFormat.explicitInt`)
    .floatBits (val &&& ((1 <<< 80) - 1))
  else if tag == 'M' then
    -- LLVM `0xM<hi64><lo64>`: preserve raw 128-bit IBM double-double pair
    .floatBits val
  else
    .floatBits val

/-- Parse an LLVM operand expression / constant (total on `fuel`). -/
def parseExp : Nat → ParseM Exp
  | 0 => throw "parse error: recursion limit exceeded in parseExp"
  | fuel + 1 => do
    let t ← bump
    match t with
    | .localId id => return .identifier (.local_id id)
    | .globalId id => return .identifier (.global_id id)
    | .intLit n => return .int n
    | .hexLit 'f' val =>
      -- `f0x<bits>`: the type's bit pattern as an APInt; a `ppc_fp128` APInt holds the high
      -- double in its low word, while `.floatBits` of `ppc_fp128` is in `0xM` order (high first)
      if (← get).lastFloatTy == some .ppc_fp128 then
        let m64 : Nat := (1 <<< 64) - 1
        return .floatBits (((val &&& m64) <<< 64) ||| (val >>> 64))
      else return .floatBits val
    | .hexLit tag val => return decodeHexFloatForType tag val
    | .fltLit neg mant exp10 => return .floatDec neg mant exp10
    | .ident "true" => return .bool true
    | .ident "false" => return .bool false
    | .ident "null" => return .null
    | .ident "zeroinitializer" => return .zeroinitializer
    | .ident "undef" => return .undef
    | .ident "poison" => return .poison
    | .ident "splat" =>
      expect .lparen "splat"
      let ty ← parseType fuel
      let e ← parseExp fuel
      expect .rparen "splat"
      return .splat (ty, e)
    | .langle =>
      -- Vector constant `<ty e1, ty e2, ...>`
      let mut elems : List (LlvmType × Exp) := []
      if !(← tryEat .rangle) then
        let mut go := true
        let mut guard := fuel
        while go && guard > 0 do
          guard := guard - 1
          let ty ← parseType fuel
          let e ← parseExp fuel
          elems := (ty, e) :: elems
          if ← tryEat .comma then go := true
          else expect .rangle "vector const"; go := false
      return .vector elems.reverse
    | .lbrack =>
      -- Array constant `[ty e1, ty e2, ...]`
      let mut elems : List (LlvmType × Exp) := []
      if !(← tryEat .rbrack) then
        let mut go := true
        let mut guard := fuel
        while go && guard > 0 do
          guard := guard - 1
          let ty ← parseType fuel
          let e ← parseExp fuel
          elems := (ty, e) :: elems
          if ← tryEat .comma then go := true
          else expect .rbrack "array const"; go := false
      return .array elems.reverse
    | .lbrace =>
      -- Struct constant `{ ty e1, ty e2, ... }`
      let mut fields : List (LlvmType × Exp) := []
      if !(← tryEat .rbrace) then
        let mut go := true
        let mut guard := fuel
        while go && guard > 0 do
          guard := guard - 1
          let ty ← parseType fuel
          let e ← parseExp fuel
          fields := (ty, e) :: fields
          if ← tryEat .comma then go := true
          else expect .rbrace "struct const"; go := false
      return .struct false fields.reverse
    | .lpacked =>
      let mut fields : List (LlvmType × Exp) := []
      if !(← tryEat .rpacked) then
        let mut go := true
        let mut guard := fuel
        while go && guard > 0 do
          guard := guard - 1
          let ty ← parseType fuel
          let e ← parseExp fuel
          fields := (ty, e) :: fields
          if ← tryEat .comma then go := true
          else expect .rpacked "packed struct const"; go := false
      return .struct true fields.reverse
    | .ident "getelementptr" =>
      let flags ← parseGEPFlags
      expect .lparen "gep constexpr"
      let baseTy ← parseType fuel
      expect .comma "gep constexpr"
      let ptrTy ← parseType fuel
      let ptrExp ← parseExp fuel
      let mut idxs : List (LlvmType × Exp) := []
      let mut guard := fuel
      while (← tryEat .comma) && guard > 0 do
        guard := guard - 1
        let _ ← tryEatIdent "inrange"
        let ity ← parseType fuel
        let iexp ← parseExp fuel
        idxs := (ity, iexp) :: idxs
      expect .rparen "gep constexpr"
      return .gepConst flags baseTy (ptrTy, ptrExp) idxs.reverse
    | .ident "ptrtoint" =>
      expect .lparen "ptrtoint constexpr"
      let fromTy ← parseType fuel
      let e ← parseExp fuel
      expectIdent "to" "ptrtoint constexpr"
      let toTy ← parseType fuel
      expect .rparen "ptrtoint constexpr"
      return .convConst .ptrtoint fromTy e toTy
    | .ident "ptrtoaddr" =>
      expect .lparen "ptrtoaddr constexpr"
      let fromTy ← parseType fuel
      let e ← parseExp fuel
      expectIdent "to" "ptrtoaddr constexpr"
      let toTy ← parseType fuel
      expect .rparen "ptrtoaddr constexpr"
      return .convConst .ptrtoaddr fromTy e toTy
    | .ident "inttoptr" =>
      expect .lparen "inttoptr constexpr"
      let fromTy ← parseType fuel
      let e ← parseExp fuel
      expectIdent "to" "inttoptr constexpr"
      let toTy ← parseType fuel
      expect .rparen "inttoptr constexpr"
      return .convConst .inttoptr fromTy e toTy
    | .ident "bitcast" =>
      expect .lparen "bitcast constexpr"
      let fromTy ← parseType fuel
      let e ← parseExp fuel
      expectIdent "to" "bitcast constexpr"
      let toTy ← parseType fuel
      expect .rparen "bitcast constexpr"
      return .convConst .bitcast fromTy e toTy
    | .ident "add" =>
      let nuw ← tryEatIdent "nuw"
      let nsw ← tryEatIdent "nsw"
      let nuw2 ← tryEatIdent "nuw"
      expect .lparen "add constexpr"
      let ty ← parseType fuel
      let v1 ← parseExp fuel
      expect .comma "add constexpr"
      let _ ← parseType fuel
      let v2 ← parseExp fuel
      expect .rparen "add constexpr"
      return .binConst (.add (nuw || nuw2) nsw) ty v1 v2
    | .ident "sub" =>
      let nuw ← tryEatIdent "nuw"
      let nsw ← tryEatIdent "nsw"
      let nuw2 ← tryEatIdent "nuw"
      expect .lparen "sub constexpr"
      let ty ← parseType fuel
      let v1 ← parseExp fuel
      expect .comma "sub constexpr"
      let _ ← parseType fuel
      let v2 ← parseExp fuel
      expect .rparen "sub constexpr"
      return .binConst (.sub (nuw || nuw2) nsw) ty v1 v2
    | .ident "mul" =>
      let nuw ← tryEatIdent "nuw"; let nsw ← tryEatIdent "nsw"; let nuw2 ← tryEatIdent "nuw"
      expect .lparen "mul constexpr"
      let ty ← parseType fuel; let v1 ← parseExp fuel
      expect .comma "mul constexpr"
      let _ ← parseType fuel; let v2 ← parseExp fuel
      expect .rparen "mul constexpr"
      return .binConst (.mul (nuw || nuw2) nsw) ty v1 v2
    | .ident "shl" =>
      let nuw ← tryEatIdent "nuw"; let nsw ← tryEatIdent "nsw"; let nuw2 ← tryEatIdent "nuw"
      expect .lparen "shl constexpr"
      let ty ← parseType fuel; let v1 ← parseExp fuel
      expect .comma "shl constexpr"
      let _ ← parseType fuel; let v2 ← parseExp fuel
      expect .rparen "shl constexpr"
      return .binConst (.shl (nuw || nuw2) nsw) ty v1 v2
    | .ident "lshr" =>
      let ex ← tryEatIdent "exact"
      expect .lparen "lshr constexpr"
      let ty ← parseType fuel; let v1 ← parseExp fuel
      expect .comma "lshr constexpr"
      let _ ← parseType fuel; let v2 ← parseExp fuel
      expect .rparen "lshr constexpr"
      return .binConst (.lshr ex) ty v1 v2
    | .ident "ashr" =>
      let ex ← tryEatIdent "exact"
      expect .lparen "ashr constexpr"
      let ty ← parseType fuel; let v1 ← parseExp fuel
      expect .comma "ashr constexpr"
      let _ ← parseType fuel; let v2 ← parseExp fuel
      expect .rparen "ashr constexpr"
      return .binConst (.ashr ex) ty v1 v2
    | .ident "and" =>
      expect .lparen "and constexpr"
      let ty ← parseType fuel; let v1 ← parseExp fuel
      expect .comma "and constexpr"
      let _ ← parseType fuel; let v2 ← parseExp fuel
      expect .rparen "and constexpr"
      return .binConst .and ty v1 v2
    | .ident "or" =>
      let disj ← tryEatIdent "disjoint"
      expect .lparen "or constexpr"
      let ty ← parseType fuel; let v1 ← parseExp fuel
      expect .comma "or constexpr"
      let _ ← parseType fuel; let v2 ← parseExp fuel
      expect .rparen "or constexpr"
      return .binConst (.or disj) ty v1 v2
    | .ident "xor" =>
      expect .lparen "xor constexpr"
      let ty ← parseType fuel; let v1 ← parseExp fuel
      expect .comma "xor constexpr"
      let _ ← parseType fuel; let v2 ← parseExp fuel
      expect .rparen "xor constexpr"
      return .binConst .xor ty v1 v2
    | .ident "trunc" =>
      let _ ← tryEatIdent "nuw"; let _ ← tryEatIdent "nsw"
      expect .lparen "trunc constexpr"
      let fromTy ← parseType fuel
      let e ← parseExp fuel
      expectIdent "to" "trunc constexpr"
      let toTy ← parseType fuel
      expect .rparen "trunc constexpr"
      return .convConst (.trunc false false) fromTy e toTy
    | .ident "zext" =>
      let _ ← tryEatIdent "nneg"
      expect .lparen "zext constexpr"
      let fromTy ← parseType fuel
      let e ← parseExp fuel
      expectIdent "to" "zext constexpr"
      let toTy ← parseType fuel
      expect .rparen "zext constexpr"
      return .convConst (.zext false) fromTy e toTy
    | .ident "sext" =>
      expect .lparen "sext constexpr"
      let fromTy ← parseType fuel
      let e ← parseExp fuel
      expectIdent "to" "sext constexpr"
      let toTy ← parseType fuel
      expect .rparen "sext constexpr"
      return .convConst .sext fromTy e toTy
    | .ident "addrspacecast" =>
      expect .lparen "addrspacecast constexpr"
      let fromTy ← parseType fuel
      let e ← parseExp fuel
      expectIdent "to" "addrspacecast constexpr"
      let toTy ← parseType fuel
      expect .rparen "addrspacecast constexpr"
      return .convConst .addrspacecast fromTy e toTy
    | .ident "blockaddress" =>
      expect .lparen "blockaddress"
      let fn ← parseRawGlobalId "blockaddress fn"
      expect .comma "blockaddress"
      let blk ← parseRawLocalId "blockaddress blk"
      expect .rparen "blockaddress"
      return .blockAddress fn blk
    | .ident "insertelement" =>
      expect .lparen "insertelement constexpr"
      let vecTy ← parseType fuel
      let vecE ← parseExp fuel
      expect .comma "insertelement constexpr"
      let elemTy ← parseType fuel
      let elemE ← parseExp fuel
      expect .comma "insertelement constexpr"
      let idxTy ← parseType fuel
      let idxE ← parseExp fuel
      expect .rparen "insertelement constexpr"
      return .insertElemConst vecTy vecE elemTy elemE idxTy idxE
    | .ident "extractelement" =>
      expect .lparen "extractelement constexpr"
      let vecTy ← parseType fuel
      let vecE ← parseExp fuel
      expect .comma "extractelement constexpr"
      let idxTy ← parseType fuel
      let idxE ← parseExp fuel
      expect .rparen "extractelement constexpr"
      return .extractElemConst vecTy vecE idxTy idxE
    | .ident "shufflevector" =>
      expect .lparen "shufflevector constexpr"
      let vecTy ← parseType fuel
      let v1 ← parseExp fuel
      expect .comma "shufflevector constexpr"
      let _ ← parseType fuel
      let v2 ← parseExp fuel
      expect .comma "shufflevector constexpr"
      let maskTy ← parseType fuel
      let maskExp ← parseExp fuel
      expect .rparen "shufflevector constexpr"
      let maskLen := match maskTy with | .vector n _ => n | _ => 1
      let mask : List (Option Nat) := match maskExp with
        | .vector es => es.map fun (_, e) => match e with | .int k => some k.toNat | _ => none
        | .zeroinitializer => List.replicate maskLen (some 0)
        | .poison | .undef => List.replicate maskLen none
        | .splat (_, .int k) => List.replicate maskLen (some k.toNat)
        | .splat _ => List.replicate maskLen none
        | _ => []
      return .shuffleVecConst vecTy v1 v2 mask
    | .ident "asm" =>
      -- Inline asm callee: `asm [sideeffect|alignstack|inteldialect|unwind]* "asm", "constraints"`
      let mut gAsm := 8
      while gAsm > 0 do
        gAsm := gAsm - 1
        match ← peek with
        | .ident "sideeffect" | .ident "alignstack" | .ident "inteldialect" | .ident "unwind" =>
          let _ ← bump
        | _ => gAsm := 0
      let _ ← bump -- asm string
      expect .comma "inline asm"
      let _ ← bump -- constraints string
      return .identifier (.global_id (.name "llvm.inlineasm.noop"))
    | .metaId _ =>
      -- Metadata operand like `!0` (used in e.g. `llvm.experimental.noalias.scope.decl(metadata !0)`)
      return .null
    | .bang =>
      -- Inline metadata node `!{...}`
      if ← tryEat .lbrace then
        let mut depth : Nat := 1
        let mut g := fuel
        while depth > 0 && g > 0 do
          g := g - 1
          match ← bump with
          | .lbrace => depth := depth + 1
          | .rbrace => depth := depth - 1
          | .eof => depth := 0
          | _ => pure ()
      return .null
    | .ident "c" =>
      match ← bump with
      | .strLit s =>
        -- Decode LLVM `c"..."` byte string with `\XX` hex escapes into `[N x i8]` array
        let rec decodeBytes : List Char → List (LlvmType × Exp)
          | [] => []
          | '\\' :: h1 :: h2 :: rest =>
            if isHexDigit h1 && isHexDigit h2 then
              (.i8, .int (Int.ofNat (hexVal h1 * 16 + hexVal h2))) :: decodeBytes rest
            else
              (.i8, .int (Int.ofNat '\\'.toNat)) :: decodeBytes (h1 :: h2 :: rest)
          | ch :: rest =>
            (.i8, .int (Int.ofNat ch.toNat)) :: decodeBytes rest
        return .array (decodeBytes s.toList)
      | tok => throw s!"parse error: expected string after 'c', got {repr tok}"
    | .ident s =>
      -- Handle `u0x...` / `s0x...` hex integer literals
      if s.startsWith "u0x" || s.startsWith "s0x" then
        let hexChars := (s.drop 3).toString.toList
        return .int (Int.ofNat (parseHexNat hexChars))
      -- Handle special float literals: `[+|-](inf|qnan|snan|nan)` with optional `(0x...)` payload
      else
        let (neg, body) :=
          if s.startsWith "-" then (true, (s.drop 1).toString)
          else if s.startsWith "+" then (false, (s.drop 1).toString)
          else (false, s)
        if body == "inf" then
          return .floatSpecial neg true false 0
        else if body == "qnan" || body == "nan" || body == "snan" then
          let quiet := body != "snan"
          let payload ←
            if ← tryEat .lparen then
              let p ← match ← bump with
                | .hexLit _ v => pure v
                | .intLit n => pure n.toNat
                | _ => pure 0
              expect .rparen "nan payload"
              pure p
            else pure 0
          return .floatSpecial neg false quiet payload
        else
          throw s!"parse error: unexpected token {repr (Tok.ident s)} in expression"
    | tok => throw s!"parse error: unexpected token {repr tok} in expression"

private def parseWrapFlags : ParseM (Bool × Bool) := do
  let mut nuw := false
  let mut nsw := false
  for _ in [0, 1] do
    if ← tryEatIdent "nuw" then nuw := true
    else if ← tryEatIdent "nsw" then nsw := true
  return (nuw, nsw)

/-! ### Metadata attachments -/

/-- Skip trailing metadata attachments like `, !dbg !12`, `, !tbaa !3`. -/
private def skipTrailingMetadata (fuel : Nat) : ParseM Unit := do
  let mut guard := 16
  while guard > 0 do
    guard := guard - 1
    match (← peek), (← peekAt 1) with
    | .comma, .metaId _ =>
      let _ ← bump -- `,`
      let _ ← bump -- `!tag`
      match ← peek with
      | .metaId _ => let _ ← bump
      | .bang =>
        let _ ← bump
        if ← tryEat .lbrace then
          let mut depth : Nat := 1
          let mut g := fuel
          while depth > 0 && g > 0 do
            g := g - 1
            match ← bump with
            | .lbrace => depth := depth + 1
            | .rbrace => depth := depth - 1
            | .eof => depth := 0
            | _ => pure ()
      | _ => pure ()
    | _, _ => guard := 0

/-- Parse the payload of a single `, !tag <payload>` metadata attachment into an optional `ValueAttr`. -/
private def parseSingleMetaAttr (fuel : Nat) (tag : String) : ParseM (Option ValueAttr) := do
  let skipBraceGroup : ParseM Unit := do
    if ← tryEat .lbrace then
      let mut depth : Nat := 1
      let mut g := fuel
      while depth > 0 && g > 0 do
        g := g - 1
        match ← bump with
        | .lbrace => depth := depth + 1
        | .rbrace => depth := depth - 1
        | .eof => depth := 0
        | _ => pure ()
  match tag with
  | "noundef" =>
    match ← peek with
    | .metaId _ => let _ ← bump
    | .bang => let _ ← bump; skipBraceGroup
    | _ => pure ()
    return some .noundef
  | "nonnull" =>
    match ← peek with
    | .metaId _ => let _ ← bump
    | .bang => let _ ← bump; skipBraceGroup
    | _ => pure ()
    return some .nonnull
  | "dereferenceable" | "dereferenceable_or_null" | "align" | "nofpclass" =>
    let n? ← match ← peek with
      | .metaId nodeId =>
        let _ ← bump
        let st ← get
        pure ((st.intMeta.find? (fun p => p.1 == nodeId)).map Prod.snd)
      | .bang =>
        let _ ← bump
        if ← tryEat .lbrace then
          let _ ← parseType fuel
          let n ← parseNatTok "meta int"
          let _ ← tryEat .rbrace
          pure (some n)
        else pure none
      | _ => pure none
    match n? with
    | some n =>
      if tag == "dereferenceable" then return some (.dereferenceable n)
      else if tag == "dereferenceable_or_null" then return some (.dereferenceableOrNull n)
      else if tag == "nofpclass" then return some (.nofpclass n)
      else return some (.align n)
    | none => return none
  | "range" =>
    match ← peek with
    | .lparen =>
      let _ ← bump
      let lo ← parseIntTok "!range lo"
      expect .comma "!range"
      let hi ← parseIntTok "!range hi"
      expect .rparen "!range"
      return some (.range lo hi)
    | .metaId nodeId =>
      let _ ← bump
      let st ← get
      match st.rangeMeta.find? (fun p => p.1 == nodeId) with
      | some (_, [(lo, hi)]) => return some (.range lo hi)
      | some (_, ps@(_ :: _)) => return some (.rangeList ps)
      | _ => return none
    | .bang =>
      let _ ← bump
      if ← tryEat .lbrace then
        let mut pairs : List (Int × Int) := []
        let mut gR := 64
        while !(← tryEat .rbrace) && gR > 0 do
          gR := gR - 1
          let _ ← parseType fuel
          let lo ← parseIntTok "!range lo"
          expect .comma "!range"
          let _ ← parseType fuel
          let hi ← parseIntTok "!range hi"
          pairs := (lo, hi) :: pairs
          let _ ← tryEat .comma
        match pairs.reverse with
        | [(lo, hi)] => return some (.range lo hi)
        | ps => return some (.rangeList ps)
      else return none
    | _ => return none
  | _ =>
    match ← peek with
    | .metaId _ => let _ ← bump
    | .bang => let _ ← bump; skipBraceGroup
    | _ => pure ()
    return none

/-- Parse all trailing `, !tag <payload>` metadata attachments into `List ValueAttr`. -/
private def parseTrailingValueAttrs (fuel : Nat) : ParseM (List ValueAttr) := do
  let mut md : List ValueAttr := []
  let mut guard := 16
  while guard > 0 do
    guard := guard - 1
    match (← peek), (← peekAt 1) with
    | .comma, .metaId tag =>
      let _ ← bump -- `,`
      let _ ← bump -- `!tag`
      if let some attr ← parseSingleMetaAttr fuel tag then
        md := attr :: md
    | _, _ => guard := 0
  return md.reverse

/-! ### Instructions -/

/-- Named calling conventions and their `cc <N>` numbers (`llvm::CallingConv`). -/
private def callingConvNames : List (String × Nat) :=
  [("ccc", 0), ("fastcc", 8), ("coldcc", 9), ("ghccc", 10), ("webkit_jscc", 12), ("anyregcc", 13),
   ("preserve_mostcc", 14), ("preserve_allcc", 15), ("swiftcc", 16), ("cxx_fast_tlscc", 17),
   ("tailcc", 18), ("cfguard_checkcc", 19), ("swifttailcc", 20), ("preserve_nonecc", 21),
   ("x86_stdcallcc", 64), ("x86_fastcallcc", 65), ("arm_apcscc", 66), ("arm_aapcscc", 67),
   ("arm_aapcs_vfpcc", 68), ("x86_thiscallcc", 70), ("ptx_kernel", 71), ("ptx_device", 72),
   ("spir_func", 75), ("spir_kernel", 76), ("intel_ocl_bicc", 77), ("x86_64_sysvcc", 78),
   ("win64cc", 79), ("x86_vectorcallcc", 80), ("x86_intrcc", 83), ("avr_intrcc", 84),
   ("avr_signalcc", 85), ("amdgpu_vs", 87), ("amdgpu_gs", 88), ("amdgpu_ps", 89),
   ("amdgpu_cs", 90), ("amdgpu_kernel", 91), ("x86_regcallcc", 92), ("amdgpu_hs", 93),
   ("aarch64_vector_pcs", 97), ("aarch64_sve_vector_pcs", 98), ("riscv_vector_cc", 110)]

/-- Parse an optional calling convention, normalized to its name (`""` for `ccc`; `cc <N>` with an
unnamed `N` stays `cc <N>`). -/
def parseCallingConv : ParseM String := do
  match ← peek with
  | .ident "cc" =>
    match ← peekAt 1 with
    | .intLit n =>
      let _ ← bump; let _ ← bump
      match callingConvNames.find? (·.2 == n.toNat) with
      | some (nm, _) => return (if nm == "ccc" then "" else nm)
      | none => return s!"cc {n}"
    | _ => return ""
  | .ident s =>
    if (callingConvNames.lookup s).isSome then
      let _ ← bump
      return (if s == "ccc" then "" else s)
    else return ""
  | _ => return ""

/-- Parse a type and, if it contains scalable vectors, also LLVM's alignment for it: the alignment
of its known-minimum layout (`vscale = 1`), which LLVM's parser records on `alloca`/`load`/`store`
without an explicit `align` (the semantic type itself is expanded with the configured `vscale`). -/
private def parseTypeScalableAlign (fuel : Nat) (pref : Bool := false) :
    ParseM (LlvmType × Option Nat) := do
  let st0 ← get
  set { st0 with vscale := 1 }
  let tyMin ← parseType fuel
  modify fun st => { st with pos := st0.pos, vscale := st0.vscale }
  let ty ← parseType fuel
  let defs := (← get).typeDefs
  let resolve (defs : List (LocalId × LlvmType)) (t : LlvmType) :=
    (resolveType defs 8 t).toOption.getD t
  let tyMin := resolve (defs.map fun (n, _, m) => (n, m)) tyMin
  let tyFull := resolve (defs.map fun (n, f, _) => (n, f)) ty
  if decide (tyMin = tyFull) then return (ty, none)
  else return (ty, some (if pref then DataLayout.default64LE.typePrefAlign tyMin
    else DataLayout.default64LE.typeABIAlign tyMin))

/-- `T v1, v2` (with trailing metadata skipped): the operands of a binary operator or compare. -/
private def parseBinaryOperands (fuel : Nat) : ParseM (LlvmType × Exp × Exp) := do
  let ty ← parseType fuel
  let v1 ← parseExp fuel
  expect .comma "binary operator"
  let v2 ← parseExp fuel
  skipTrailingMetadata fuel
  return (ty, v1, v2)

/-- `T v to T'` (with trailing metadata skipped): the operands of a cast. -/
private def parseCastOperands (fuel : Nat) : ParseM (LlvmType × Exp × LlvmType) := do
  let fromTy ← parseType fuel
  let v ← parseExp fuel
  expectIdent "to" "cast"
  let toTy ← parseType fuel
  skipTrailingMetadata fuel
  return (fromTy, v, toTy)

/-- For an integer binary opcode, the parser of its flags (`nuw`/`nsw`, `exact`, `disjoint`). -/
private def intBinaryOpParser? : String → Option (ParseM IntBinaryOp)
  | "add" => some do let (nuw, nsw) ← parseWrapFlags; return .add nuw nsw
  | "sub" => some do let (nuw, nsw) ← parseWrapFlags; return .sub nuw nsw
  | "mul" => some do let (nuw, nsw) ← parseWrapFlags; return .mul nuw nsw
  | "shl" => some do let (nuw, nsw) ← parseWrapFlags; return .shl nuw nsw
  | "udiv" => some do return .udiv (← tryEatIdent "exact")
  | "sdiv" => some do return .sdiv (← tryEatIdent "exact")
  | "lshr" => some do return .lshr (← tryEatIdent "exact")
  | "ashr" => some do return .ashr (← tryEatIdent "exact")
  | "or" => some do return .or (← tryEatIdent "disjoint")
  | "urem" => some (pure .urem)
  | "srem" => some (pure .srem)
  | "and" => some (pure .and)
  | "xor" => some (pure .xor)
  | _ => none

/-- For a floating-point binary opcode, the parser of its fast-math flags. -/
private def floatBinaryOpParser? : String → Option (ParseM FloatBinaryOp)
  | "fadd" => some do return .fadd (← parseFMF)
  | "fsub" => some do return .fsub (← parseFMF)
  | "fmul" => some do return .fmul (← parseFMF)
  | "fdiv" => some do return .fdiv (← parseFMF)
  | "frem" => some do return .frem (← parseFMF)
  | _ => none

/-- For a cast opcode, the parser of its flags. -/
private def conversionOpParser? : String → Option (ParseM ConversionOp)
  | "trunc" => some do let (nuw, nsw) ← parseWrapFlags; return .trunc nuw nsw
  | "zext" => some do return .zext (← tryEatIdent "nneg")
  | "uitofp" => some do
    let nneg ← tryEatIdent "nneg"
    return .uitofp nneg (← parseFMF)
  | "fptrunc" => some do return .fptrunc (← parseFMF)
  | "fpext" => some do return .fpext (← parseFMF)
  | "sitofp" => some do return .sitofp (← parseFMF)
  | "sext" => some (pure .sext)
  | "fptoui" => some (pure .fptoui)
  | "fptosi" => some (pure .fptosi)
  | "ptrtoint" => some (pure .ptrtoint)
  | "ptrtoaddr" => some (pure .ptrtoaddr)
  | "inttoptr" => some (pure .inttoptr)
  | "bitcast" => some (pure .bitcast)
  | "addrspacecast" => some (pure .addrspacecast)
  | _ => none

/-- Parse an instruction other than a binary operator or a cast, after its opcode `opTok`. -/
private def parseOtherInstruction (fuel : Nat) (isTail : Bool) (opTok : Tok) : ParseM Instruction := do
  match opTok with
  | .ident "fneg" =>
    let fmf ← parseFMF
    let ty ← parseType fuel
    let v ← parseExp fuel
    skipTrailingMetadata fuel
    return .floatUnaryOp (.fneg fmf) ty v
  | .ident "icmp" =>
    let samesign ← tryEatIdent "samesign"
    let pred ← parseICmpPred "icmp"
    let (ty, v1, v2) ← parseBinaryOperands fuel
    return .icmp samesign pred ty v1 v2
  | .ident "fcmp" =>
    let fmf ← parseFMF
    let pred ← parseFCmpPred "fcmp"
    let (ty, v1, v2) ← parseBinaryOperands fuel
    return .fcmp fmf pred ty v1 v2
  | .ident "select" =>
    let fmf ← parseFMF
    let cty ← parseType fuel
    let cond ← parseExp fuel
    expect .comma "select"
    let vty ← parseType fuel
    let tv ← parseExp fuel
    expect .comma "select"
    let _ ← parseType fuel
    let fv ← parseExp fuel
    skipTrailingMetadata fuel
    return .select fmf cty cond vty tv fv
  | .ident "phi" =>
    let fmf ← parseFMF
    let ty ← parseType fuel
    let mut incoming : List (Exp × BlockId) := []
    let mut go := true
    let mut guard := fuel
    while go && guard > 0 do
      guard := guard - 1
      expect .lbrack "phi"
      let val ← parseExp fuel
      expect .comma "phi"
      let blk ← parseRawLocalId "phi block"
      expect .rbrack "phi"
      incoming := (val, blk) :: incoming
      if !(← tryEat .comma) then go := false
      else
        match ← peek with
        | .metaId _ =>
          modify fun st => { st with pos := st.pos - 1 }
          go := false
        | _ => pure ()
    let md ← parseTrailingValueAttrs fuel
    return .phi ty fmf incoming.reverse md
  | .ident "freeze" =>
    let ty ← parseType fuel
    let e ← parseExp fuel
    skipTrailingMetadata fuel
    return .freeze (ty, e)
  | .ident "bitinsert" =>
    let baseTy ← parseType fuel
    let base ← parseExp fuel
    expect .comma "bitinsert"
    let valTy ← parseType fuel
    let val ← parseExp fuel
    expect .comma "bitinsert"
    let offTy ← parseType fuel
    let off ← parseExp fuel
    skipTrailingMetadata fuel
    return .bitinsert baseTy base valTy val offTy off
  | .ident "bitextract" =>
    let retTy ← parseType fuel
    expect .comma "bitextract"
    let srcTy ← parseType fuel
    let src ← parseExp fuel
    expect .comma "bitextract"
    let offTy ← parseType fuel
    let off ← parseExp fuel
    skipTrailingMetadata fuel
    return .bitextract retTy srcTy src offTy off
  | .ident "alloca" =>
    let _ ← tryEatIdent "inalloca"
    let (allocTy, scalableAlign?) ← parseTypeScalableAlign fuel (pref := true)
    let mut numElem : Option (LlvmType × Exp) := none
    let mut align? : Option Nat := none
    let mut addrSpace : Nat := 0
    let mut guard := 8
    while (← tryEat .comma) && guard > 0 do
      guard := guard - 1
      match ← peek with
      | .ident "align" =>
        let _ ← bump
        align? := some (← parseNatTok "alloca align")
      | .ident "addrspace" =>
        let _ ← bump
        expect .lparen "alloca addrspace"
        addrSpace ← parseNatTok "alloca addrspace"
        expect .rparen "alloca addrspace"
      | .metaId _ =>
        -- Rewind comma for skipTrailingMetadata
        modify fun st => { st with pos := st.pos - 1 }
        guard := 0
      | _ =>
        let cty ← parseType fuel
        let cexp ← parseExp fuel
        numElem := some (cty, cexp)
    skipTrailingMetadata fuel
    return .alloca allocTy numElem (align?.orElse fun _ => scalableAlign?) addrSpace
  | .ident "load" =>
    let _ ← tryEatIdent "atomic"
    let isVol ← tryEatIdent "volatile"
    let (ty, scalableAlign?) ← parseTypeScalableAlign fuel
    expect .comma "load"
    let ptrTy ← parseType fuel
    let ptrExp ← parseExp fuel
    let mut align? : Option Nat := none
    let mut noundef : Bool := false
    let mut md : List ValueAttr := []
    let mut guard := 16
    while (← tryEat .comma) && guard > 0 do
      guard := guard - 1
      match ← peek with
      | .ident "align" =>
        let _ ← bump
        align? := some (← parseNatTok "load align")
      | .metaId tag =>
        let _ ← bump
        if let some attr ← parseSingleMetaAttr fuel tag then
          if attr == .noundef then noundef := true
          else md := attr :: md
      | _ => guard := 0
    return .load ty ptrTy ptrExp (align?.orElse fun _ => scalableAlign?) isVol noundef md.reverse
  | .ident "store" =>
    let _ ← tryEatIdent "atomic"
    let isVol ← tryEatIdent "volatile"
    let (valTy, scalableAlign?) ← parseTypeScalableAlign fuel
    let valExp ← parseExp fuel
    expect .comma "store"
    let ptrTy ← parseType fuel
    let ptrExp ← parseExp fuel
    let mut align? : Option Nat := none
    if (← peek) == .comma && (← peekAt 1) == .ident "align" then
      let _ ← bump
      let _ ← bump
      align? := some (← parseNatTok "store align")
    skipTrailingMetadata fuel
    return .store valTy valExp ptrTy ptrExp (align?.orElse fun _ => scalableAlign?) isVol
  | .ident "getelementptr" =>
    let flags ← parseGEPFlags
    let baseTy ← parseType fuel
    expect .comma "gep"
    let ptrTy ← parseType fuel
    let ptrExp ← parseExp fuel
    let mut idxs : List (LlvmType × Exp) := []
    let mut guard := fuel
    while (← peek) == .comma && guard > 0 do
      guard := guard - 1
      match ← peekAt 1 with
      | .metaId _ => guard := 0
      | _ =>
        let _ ← bump
        let _ ← tryEatIdent "inrange"
        let ity ← parseType fuel
        let iexp ← parseExp fuel
        idxs := (ity, iexp) :: idxs
    skipTrailingMetadata fuel
    return .getelementptr flags baseTy ptrTy ptrExp idxs.reverse
  | .ident "extractvalue" =>
    let aggTy ← parseType fuel
    let agg ← parseExp fuel
    let mut idxs : List Nat := []
    let mut guard := 16
    while (← peek) == .comma && guard > 0 do
      guard := guard - 1
      match ← peekAt 1 with
      | .metaId _ => guard := 0
      | _ =>
        let _ ← bump
        idxs := (← parseNatTok "extractvalue idx") :: idxs
    skipTrailingMetadata fuel
    return .extractvalue aggTy agg idxs.reverse
  | .ident "insertvalue" =>
    let aggTy ← parseType fuel
    let agg ← parseExp fuel
    expect .comma "insertvalue"
    let valTy ← parseType fuel
    let val ← parseExp fuel
    let mut idxs : List Nat := []
    let mut guard := 16
    while (← peek) == .comma && guard > 0 do
      guard := guard - 1
      match ← peekAt 1 with
      | .metaId _ => guard := 0
      | _ =>
        let _ ← bump
        idxs := (← parseNatTok "insertvalue idx") :: idxs
    skipTrailingMetadata fuel
    return .insertvalue aggTy agg valTy val idxs.reverse
  | .ident "extractelement" =>
    let vecTy ← parseType fuel
    let vec ← parseExp fuel
    expect .comma "extractelement"
    let idxTy ← parseType fuel
    let idx ← parseExp fuel
    skipTrailingMetadata fuel
    return .extractelement vecTy vec idxTy idx
  | .ident "insertelement" =>
    let vecTy ← parseType fuel
    let vec ← parseExp fuel
    expect .comma "insertelement"
    let valTy ← parseType fuel
    let val ← parseExp fuel
    expect .comma "insertelement"
    let idxTy ← parseType fuel
    let idx ← parseExp fuel
    skipTrailingMetadata fuel
    return .insertelement vecTy vec valTy val idxTy idx
  | .ident "shufflevector" =>
    let vecTy ← parseType fuel
    let v1 ← parseExp fuel
    expect .comma "shufflevector"
    let _ ← parseType fuel
    let v2 ← parseExp fuel
    expect .comma "shufflevector"
    let maskTy ← parseType fuel -- mask vector type `<M x i32>`
    let maskLen : Nat := match maskTy with | .vector m _ => m | _ => 0
    let maskExp ← parseExp fuel
    skipTrailingMetadata fuel
    let mask : List (Option Nat) := match maskExp with
      | .vector elems => elems.map fun (_, e) => match e with
        | .int n => if n ≥ 0 then some n.toNat else none
        | _ => none
      | .zeroinitializer => List.replicate maskLen (some 0)
      | .splat (_, .int n) => List.replicate maskLen (if n ≥ 0 then some n.toNat else none)
      | .splat (_, .poison) | .poison => List.replicate maskLen none
      | _ => []
    return .shufflevector vecTy v1 v2 mask
  | .ident "call" =>
    let fmf ← parseFMF
    -- Optional calling convention
    let cc ← parseCallingConv
    let retAttrs ← parseValueAttrs fuel
    let retTy ← parseRetType fuel
    -- Optional explicit function type `(argTys[, ...])` before `@callee` (the call's type must
    -- equal the callee's, LangRef `call`)
    let explicitTy? : Option (List LlvmType × Bool) ← do
      if ← tryEat .lparen then
        let mut tys : List LlvmType := []
        let mut va := false
        let mut g := fuel
        while !(← tryEat .rparen) && g > 0 do
          g := g - 1
          if ← tryEat .ellipsis then va := true
          else
            let t ← parseType fuel
            tys := t :: tys
          let _ ← tryEat .comma
        pure (some (tys.reverse, va))
      else pure none
    let callee ← parseExp fuel
    expect .lparen "call args"
    let mut args : List (LlvmType × Exp × List ValueAttr) := []
    if !(← tryEat .rparen) then
      let mut go := true
      let mut guard := fuel
      while go && guard > 0 do
        guard := guard - 1
        let ty ← parseType fuel
        let attrs ← parseValueAttrs fuel
        let e ← parseExp fuel
        args := (ty, e, attrs) :: args
        if ← tryEat .comma then go := true
        else expect .rparen "call args"; go := false
    -- Optional operand bundles `[ "tag"(ty1 e1, ...), ... ]`
    let mut bundles : List (String × List (LlvmType × Exp)) := []
    if ← tryEat .lbrack then
      if !(← tryEat .rbrack) then
        let mut goB := true
        let mut gB := fuel
        while goB && gB > 0 do
          gB := gB - 1
          let tag ← match ← bump with
            | .strLit s => pure s
            | t => throw s!"parse error (operand bundle): expected string tag, got {repr t}"
          expect .lparen "operand bundle args"
          let mut bargs : List (LlvmType × Exp) := []
          if !(← tryEat .rparen) then
            let mut goBA := true
            let mut gBA := fuel
            while goBA && gBA > 0 do
              gBA := gBA - 1
              let bty ← parseType fuel
              let be ← parseExp fuel
              bargs := (bty, be) :: bargs
              if ← tryEat .comma then goBA := true
              else expect .rparen "operand bundle args"; goBA := false
          bundles := (tag, bargs.reverse) :: bundles
          if ← tryEat .comma then goB := true
          else expect .rbrack "operand bundles"; goB := false
    -- Optional trailing call-site function attributes (`#0`, `nounwind`, `noreturn`, etc.)
    let mut isNoRet := false
    let mut g2 := 16
    while g2 > 0 do
      g2 := g2 - 1
      match ← peek with
      | .attrGrp n =>
        let _ ← bump
        let st ← get
        if st.noReturnGrps.contains n then isNoRet := true
      | .ident "noreturn" =>
        let _ ← bump
        isNoRet := true
      | .ident "nounwind" | .ident "readonly" | .ident "readnone" | .ident "willreturn"
      | .ident "memory" | .ident "convergent" | .ident "cold" | .ident "nobuiltin" =>
        let _ ← bump; skipParenGroup fuel
      | _ => g2 := 0
    let callMd ← parseTrailingValueAttrs fuel
    return .call retTy fmf callee args.reverse (retAttrs ++ callMd) bundles.reverse isNoRet
      { isTail := isTail, callingConv := cc,
        fnTy? := some (match explicitTy? with
          | some (tys, va) => .function retTy tys va
          | none => .function retTy (args.reverse.map (·.1)) false) }
  | tok => throw s!"parse error: unsupported instruction opcode {repr tok}"

/-- Parse a single non-terminator LLVM instruction. -/
def parseInstruction (fuel : Nat) : ParseM Instruction := do
  -- Handle optional `tail` / `musttail` / `notail` prefix on `call`
  let isTail1 ← tryEatIdent "tail"
  let isTail2 ← tryEatIdent "musttail"
  let _ ← tryEatIdent "notail"
  let isTail := isTail1 || isTail2
  let opTok ← bump
  match opTok with
  | .ident op =>
    if let some parseOp := intBinaryOpParser? op then
      let op ← parseOp
      let (ty, v1, v2) ← parseBinaryOperands fuel
      return .intBinaryOp op ty v1 v2
    else if let some parseOp := floatBinaryOpParser? op then
      let op ← parseOp
      let (ty, v1, v2) ← parseBinaryOperands fuel
      return .floatBinaryOp op ty v1 v2
    else if let some parseOp := conversionOpParser? op then
      let op ← parseOp
      let (fromTy, v, toTy) ← parseCastOperands fuel
      return .conversionOp op fromTy v toTy
    else parseOtherInstruction fuel isTail opTok
  | _ => parseOtherInstruction fuel isTail opTok

/-! ### Terminators and basic blocks -/

private def isTerminatorStart : Tok → Bool
  | .ident "ret" | .ident "br" | .ident "switch" | .ident "indirectbr"
  | .ident "unreachable" | .ident "resume" => true
  | _ => false

/-- Parse a block terminator. -/
def parseTerminator (fuel : Nat) : ParseM Terminator := do
  match ← bump with
  | .ident "ret" =>
    if ← tryEatIdent "void" then
      skipTrailingMetadata fuel
      return .retVoid
    else
      let ty ← parseType fuel
      let e ← parseExp fuel
      skipTrailingMetadata fuel
      return .ret (ty, e)
  | .ident "br" =>
    if ← tryEatIdent "label" then
      let dest ← parseRawLocalId "br label"
      skipTrailingMetadata fuel
      return .br dest
    else
      let _ ← parseType fuel -- `i1`
      let cond ← parseExp fuel
      expect .comma "condBr"
      expectIdent "label" "condBr true"
      let tDest ← parseRawLocalId "condBr true"
      expect .comma "condBr"
      expectIdent "label" "condBr false"
      let fDest ← parseRawLocalId "condBr false"
      skipTrailingMetadata fuel
      return .condBr cond tDest fDest
  | .ident "switch" =>
    let ty ← parseType fuel
    let cond ← parseExp fuel
    expect .comma "switch"
    expectIdent "label" "switch default"
    let dflt ← parseRawLocalId "switch default"
    expect .lbrack "switch cases"
    let mut cases : List (Int × BlockId) := []
    let mut guard := fuel
    while !(← tryEat .rbrack) && guard > 0 do
      guard := guard - 1
      let _ ← parseType fuel
      let v ← parseIntTok "switch case val"
      expect .comma "switch case"
      expectIdent "label" "switch case label"
      let lbl ← parseRawLocalId "switch case label"
      cases := (v, lbl) :: cases
    skipTrailingMetadata fuel
    return .switch ty cond dflt cases.reverse
  | .ident "indirectbr" =>
    let _ ← parseType fuel -- `ptr`
    let addr ← parseExp fuel
    expect .comma "indirectbr"
    expect .lbrack "indirectbr dests"
    let mut dests : List BlockId := []
    if !(← tryEat .rbrack) then
      let mut go := true
      let mut guard := fuel
      while go && guard > 0 do
        guard := guard - 1
        expectIdent "label" "indirectbr label"
        let lbl ← parseRawLocalId "indirectbr label"
        dests := lbl :: dests
        if ← tryEat .comma then go := true
        else expect .rbrack "indirectbr dests"; go := false
    skipTrailingMetadata fuel
    return .indirectBr addr dests.reverse
  | .ident "resume" =>
    let _ ← parseType fuel
    let _ ← parseExp fuel
    skipTrailingMetadata fuel
    return .unreachable
  | .ident "unreachable" =>
    skipTrailingMetadata fuel
    return .unreachable
  | tok => throw s!"parse error: expected terminator, got {repr tok}"

/-- Check whether the current position starts a basic block label (`name:` or `0:`). -/
private def isBlockLabelStart : ParseM Bool := do
  match (← peek), (← peekAt 1) with
  | .ident _, .colon => return true
  | .intLit _, .colon => return true
  | _, _ => return false

private def parseBlockLabel : ParseM BlockId := do
  let t ← bump
  expect .colon "block label"
  match t with
  | .ident s => return .name s
  | .intLit n => return .anonymous n.toNat
  | _ => throw s!"parse error: invalid block label {repr t}"

/-- Parse an `invoke` or `callbr` terminator, desugaring into a `call` instruction + `br label %normal`. -/
private def parseInvoke (fuel : Nat) (iid? : Option InstructionId) :
    ParseM ((InstructionId × Instruction) × Terminator) := do
  let isCallBr ← tryEatIdent "callbr"
  if !isCallBr then expectIdent "invoke" "invoke"
  let fmf ← parseFMF
  let cc ← parseCallingConv
  let retAttrs ← parseValueAttrs fuel
  let retTy ← parseRetType fuel
  if (← peek) == .lparen then skipParenGroup fuel
  let callee ← parseExp fuel
  expect .lparen "invoke args"
  let mut args : List (LlvmType × Exp × List ValueAttr) := []
  if !(← tryEat .rparen) then
    let mut go := true
    let mut guard := fuel
    while go && guard > 0 do
      guard := guard - 1
      let ty ← parseType fuel
      let attrs ← parseValueAttrs fuel
      let e ← parseExp fuel
      args := (ty, e, attrs) :: args
      if ← tryEat .comma then go := true
      else expect .rparen "invoke args"; go := false
  let mut isNoRet := false
  let mut gA := 16
  while gA > 0 do
    gA := gA - 1
    match ← peek with
    | .attrGrp n =>
      let _ ← bump
      let st ← get
      if st.noReturnGrps.contains n then isNoRet := true
    | .ident "noreturn" => let _ ← bump; isNoRet := true
    | .ident "nounwind" | .ident "readonly" | .ident "readnone" | .ident "willreturn" | .ident "nobuiltin"
    | .ident "memory" | .ident "convergent" | .ident "cold" => let _ ← bump; skipParenGroup fuel
    | _ => gA := 0
  expectIdent "to" "invoke to"
  expectIdent "label" "invoke normal label"
  let normalLbl ← parseRawLocalId "invoke normal label"
  if isCallBr then
    -- `callbr ... to label %normal [label %indirect1, ...]`
    if ← tryEat .lbrack then
      let mut gCB := fuel
      while !(← tryEat .rbrack) && gCB > 0 do
        gCB := gCB - 1
        let _ ← bump
  else
    expectIdent "unwind" "invoke unwind"
    expectIdent "label" "invoke unwind label"
    let _ ← parseRawLocalId "invoke unwind label"
  skipTrailingMetadata fuel
  let iid ← match iid? with
    | some id => pure id
    | none => match retTy with | .void => freshVoidId | .ret _ => pure (InstructionId.id (← freshAnonId))
  return ((iid, .call retTy fmf callee args.reverse retAttrs [] isNoRet { callingConv := cc }), .br normalLbl)

/-- Parse a single basic block (with explicit or implicit label). -/
def parseBlock (fuel : Nat) (isFirst : Bool) : ParseM Block := do
  let bid ←
    if ← isBlockLabelStart then parseBlockLabel
    else if isFirst then
      -- LLVM gives an unlabeled entry block the next unnamed slot number (%0, or %N after N
      -- unnamed parameters), and `phi`/`br` refer to it by that number.
      freshAnonId
    else throw s!"parse error: expected block label, got {repr (← peek)}"
  let mut code : List (InstructionId × Instruction) := []
  let mut term? : Option (InstructionId × Terminator) := none
  let mut guard := fuel
  while term?.isNone && guard > 0 do
    guard := guard - 1
    let p0 := (← get).pos
    let n0 := code.length
    let t0 ← peek
    if isTerminatorStart t0 then
      let term ← parseTerminator fuel
      let vid ← freshVoidId
      term? := some (vid, term)
    else if t0 == .ident "invoke" || t0 == .ident "callbr" then
      let (callPair, brTerm) ← parseInvoke fuel none
      code := callPair :: code
      let vid ← freshVoidId
      term? := some (vid, brTerm)
    else if t0 == .ident "landingpad" then
      let _ ← bump
      let lpTy ← parseType fuel
      let mut gLP := 16
      while gLP > 0 do
        gLP := gLP - 1
        match ← peek with
        | .ident "cleanup" => let _ ← bump
        | .ident "catch" | .ident "filter" =>
          let _ ← bump; let _ ← parseType fuel; let _ ← parseExp fuel
        | _ => gLP := 0
      let iid ← pure (InstructionId.id (← freshAnonId))
      code := (iid, .freeze (lpTy, .poison)) :: code
    else
      match t0, (← peekAt 1) with
      | .localId id, .eq =>
        let _ ← bump -- `%id`
        let _ ← bump -- `=`
        if (← peek) == .ident "invoke" || (← peek) == .ident "callbr" then
          let (callPair, brTerm) ← parseInvoke fuel (some (.id id))
          code := callPair :: code
          let vid ← freshVoidId
          term? := some (vid, brTerm)
        else if (← peek) == .ident "landingpad" then
          let _ ← bump
          let lpTy ← parseType fuel
          -- Skip `cleanup` / `catch <ty> <val>` / `filter <ty> <val>` clauses
          let mut gLP := 16
          while gLP > 0 do
            gLP := gLP - 1
            match ← peek with
            | .ident "cleanup" => let _ ← bump
            | .ident "catch" | .ident "filter" =>
              let _ ← bump; let _ ← parseType fuel; let _ ← parseExp fuel
            | _ => gLP := 0
          code := (.id id, .freeze (lpTy, .poison)) :: code
        else
          let instr ← parseInstruction fuel
          code := (.id id, instr) :: code
      | _, _ =>
        let instr ← parseInstruction fuel
        let iid ← match instr with
          | .store .. | .call .void .. => freshVoidId
          | _ => pure (.id (← freshAnonId))
        code := (iid, instr) :: code
    let p1 := (← get).pos
    let line := (← get).lines.getD p0 0
    if code.length != n0 then
      match code with
      | (iid, _) :: _ =>
        modify fun st => { st with curSrc := st.curSrc.push { iid, startTok := p0, endTok := p1, line } }
      | [] => pure ()
    match term? with
    | some (tid, _) =>
      modify fun st => { st with curSrc := st.curSrc.push { iid := tid, startTok := p0, endTok := p1, line } }
    | none => pure ()
  match term? with
  | some term => return { id := bid, code := code.reverse, terminator := term }
  | none => throw s!"parse error: block '{bid.toString}' missing terminator"

/-! ### Function headers -/

/-- Skip optional LLVM linkage / visibility / dll / unnamed_addr keywords. -/
private def skipLinkageAndCC : ParseM Unit := do
  let mut guard := 16
  while guard > 0 do
    guard := guard - 1
    match ← peek with
    | .ident "private" | .ident "internal" | .ident "available_externally"
    | .ident "linkonce" | .ident "weak" | .ident "common" | .ident "appending"
    | .ident "extern_weak" | .ident "linkonce_odr" | .ident "weak_odr"
    | .ident "external" | .ident "dso_local" | .ident "dso_preemptable"
    | .ident "default" | .ident "hidden" | .ident "protected"
    | .ident "unnamed_addr" | .ident "local_unnamed_addr"
    | .ident "thread_local" | .ident "externally_initialized" =>
      let _ ← bump
    | _ => guard := 0

/-- Parse/skip optional function-level attributes (`#0`, `nounwind`, `noreturn`, `nobuiltin`, etc.),
    returning `(isNoReturn, isNoBuiltin)`. -/
private def parseDenormKind : String → Option DenormalModeKind
  | "positivezero" | "positive-zero" => some .positiveZero
  | "preservesign" | "preserve-sign" => some .preserveSign
  | "ieee" => some .ieee
  | _ => none

/-- The tokens inside `denormal_fpenv(...)`: `[out[|in]] [, float: out[|in]]` (LangRef
`denormal_fpenv`; one mode sets both output and input). Returns (general mode, `float:` mode). -/
def denormFromToks (ts : List Tok) : Option DenormalMode × Option DenormalMode :=
  let segs := (ts.foldr (init := [[]]) fun t acc =>
    if t == .comma then [] :: acc else match acc with
      | seg :: rest => (t :: seg) :: rest
      | [] => [[t]])
  let mode (kinds : List DenormalModeKind) : Option DenormalMode :=
    match kinds with
    | [m] => some { input := m, output := m }
    | [outM, inM] => some { input := inM, output := outM }
    | _ => none
  let kindsOf (seg : List Tok) : List DenormalModeKind :=
    seg.filterMap fun | .ident s => parseDenormKind s | _ => none
  segs.foldl (init := (none, none)) fun (g, f) seg =>
    match seg with
    | .ident "float" :: .colon :: rest => (g, mode (kindsOf rest))
    | _ => (mode (kindsOf seg), f)

private def skipFnAttrs (fuel : Nat) :
    ParseM (Bool × Bool × Option DenormalMode × Option DenormalMode × Option FunctionId) := do
  let mut personality? : Option FunctionId := none
  let mut isNoRet := false
  let mut isNoBuiltin := false
  let mut denorm? : Option DenormalMode := none
  let mut denormF32? : Option DenormalMode := none
  let mut guard := 32
  while guard > 0 do
    guard := guard - 1
    match ← peek with
    | .attrGrp n =>
      let _ ← bump
      let st ← get
      if st.noReturnGrps.contains n then isNoRet := true
      -- `denormal_fpenv` inside the group (`attributes #n = { denormal_fpenv(...) }`)
      if let some (_, g?, f?) := st.denormGrps.find? (·.1 == n) then
        if g?.isSome then denorm? := g?
        if f?.isSome then denormF32? := f?
    | .ident "noreturn" =>
      let _ ← bump
      isNoRet := true
    | .ident "nobuiltin" =>
      let _ ← bump
      isNoBuiltin := true
    | .ident "denormal_fpenv" =>
      let _ ← bump
      if ← tryEat .lparen then
        let mut inner : List Tok := []
        let mut depth : Nat := 1
        let mut g := fuel
        while depth > 0 && g > 0 do
          g := g - 1
          let t ← bump
          match t with
          | .lparen => depth := depth + 1
          | .rparen => depth := depth - 1
          | .eof => depth := 0
          | _ => pure ()
          if depth > 0 then inner := t :: inner
        let (g?, f?) := denormFromToks inner.reverse
        if g?.isSome then denorm? := g?
        if f?.isSome then denormF32? := f?
    | .ident "unnamed_addr" | .ident "local_unnamed_addr" | .ident "nounwind"
    | .ident "readonly" | .ident "readnone" | .ident "willreturn"
    | .ident "alwaysinline" | .ident "noinline" | .ident "optnone" | .ident "optsize"
    | .ident "memory" | .ident "convergent" | .ident "cold" | .ident "hot"
    | .ident "nofree" | .ident "nosync" | .ident "uwtable" | .ident "ssp"
    | .ident "speculatable" | .ident "mustprogress"
    | .ident "argmemonly" | .ident "inaccessiblememonly" | .ident "presplitcoroutine" =>
      let _ ← bump
      skipParenGroup fuel
    | .ident "align" =>
      let _ ← bump
      let _ ← parseNatTok "fn align"
    | .ident "section" | .ident "comdat" =>
      let _ ← bump
      let _ ← bump
    | .ident "personality" =>
      let _ ← bump
      let _ ← parseType fuel
      match ← parseExp fuel with
      | .identifier (.global_id g) => personality? := some g
      | _ => pure ()
    | .ident "addrspace" =>
      let _ ← bump
      skipParenGroup fuel
    | .strLit _ =>
      let _ ← bump
      if ← tryEat .eq then let _ ← bump
    | _ => guard := 0
  return (isNoRet, isNoBuiltin, denorm?, denormF32?, personality?)

/-- Parse a `declare` or `define` header returning `(Declaration, paramNames)`. -/
private def parseFnHeader (fuel : Nat) : ParseM (Declaration × List LocalId) := do
  skipLinkageAndCC
  let cc ← parseCallingConv
  skipLinkageAndCC
  let retAttrs ← parseValueAttrs fuel
  let retTy ← parseRetType fuel
  let fnName ← parseRawGlobalId "function name"
  expect .lparen "function params"
  let mut argTys : List LlvmType := []
  let mut argAttrs : List (List ValueAttr) := []
  let mut argNames : List LocalId := []
  let mut isVarArg := false
  let mut anonIdx : Nat := 0
  if !(← tryEat .rparen) then
    let mut go := true
    let mut guard := fuel
    while go && guard > 0 do
      guard := guard - 1
      if ← tryEat .ellipsis then
        isVarArg := true
        expect .rparen "vararg function params"
        go := false
      else
        let ty ← parseType fuel
        let attrs ← parseValueAttrs fuel
        let nm ←
          match ← peek with
          | .localId id => let _ ← bump; pure id
          | _ =>
            let id := RawId.anonymous anonIdx
            anonIdx := anonIdx + 1
            pure id
        argTys := ty :: argTys
        argAttrs := attrs :: argAttrs
        argNames := nm :: argNames
        if ← tryEat .comma then go := true
        else expect .rparen "function params"; go := false
  let (isNoRet, isNoBuiltin, denorm?, denormF32?, personality?) ← skipFnAttrs fuel
  let decl : Declaration := {
    name := fnName
    type := .function retTy argTys.reverse isVarArg
    argAttrs := argAttrs.reverse
    retAttrs := retAttrs
    isNoReturn := isNoRet
    isNoBuiltin := isNoBuiltin
    denormalMode := denorm?
    denormalModeF32 := denormF32?
    callingConv := cc
    personality? := personality?
  }
  return (decl, argNames.reverse)

/-! ### Modules -/

/-- Result of parsing a standalone `.ll` file. -/
structure ParsedModule where
  topLevel   : TopLevel
  dataLayout : DataLayout := .default64LE
  /-- Token stream of the source (for source-faithful printing). -/
  tokens     : Array Tok := #[]
  /-- Per-function source map (token ranges and line numbers of instructions). -/
  fnSrcs     : Array FnSrc := #[]
deriving Repr

/-- Pre-scan `!N = !{ i32 lo, i32 hi }` metadata nodes so `load ... !range !N` resolves cleanly. -/
private def prescanRangeMetadata (toks : Array Tok) : List (String × List (Int × Int)) :=
  let n := toks.size
  -- `ty v, ty v, ...}` starting at `j`: the integers, or `none` if the node is not of that form.
  let rec ints (j : Nat) (fuel : Nat) (acc : List Int) : Option (List Int × Nat) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match toks.getD j .eof, toks.getD (j + 1) .eof, toks.getD (j + 2) .eof with
      | .ident _, .intLit v, .comma => ints (j + 3) fuel (v :: acc)
      | .ident _, .intLit v, .rbrace => some ((v :: acc).reverse, j + 3)
      | _, _, _ => none
  let rec pairs : List Int → List (Int × Int)
    | lo :: hi :: rest => (lo, hi) :: pairs rest
    | _ => []
  let rec go (i : Nat) (acc : List (String × List (Int × Int))) : List (String × List (Int × Int)) :=
    if i + 4 ≥ n then acc
    else
      match toks.getD i .eof, toks.getD (i + 1) .eof, toks.getD (i + 2) .eof, toks.getD (i + 3) .eof with
      | .metaId id, .eq, .bang, .lbrace =>
        match ints (i + 4) 64 [] with
        | some (vs, _) =>
          if vs.length ≥ 2 && vs.length % 2 == 0 then go (i + 4) ((id, pairs vs) :: acc)
          else go (i + 4) acc
        | none => go (i + 1) acc
      | _, _, _, _ => go (i + 1) acc
  termination_by n - i
  go 0 []

/-- Pre-scan `!N = !{ i64 val }` single-integer metadata nodes (for `!dereferenceable`, `!align`). -/
private def prescanIntMetadata (toks : Array Tok) : List (String × Nat) :=
  let n := toks.size
  let rec go (i : Nat) (acc : List (String × Nat)) : List (String × Nat) :=
    if i + 6 ≥ n then acc
    else
      match toks.getD i .eof, toks.getD (i + 1) .eof, toks.getD (i + 2) .eof,
            toks.getD (i + 3) .eof, toks.getD (i + 4) .eof, toks.getD (i + 5) .eof,
            toks.getD (i + 6) .eof with
      | .metaId id, .eq, .bang, .lbrace, .ident _, .intLit v, .rbrace =>
        go (i + 7) ((id, v.toNat) :: acc)
      | _, _, _, _, _, _, _ =>
        go (i + 1) acc
  termination_by n - i
  go 0 []

/-- Pre-scan `attributes #N = { ... noreturn ... }` attribute groups. -/
private def prescanNoReturnGroups (toks : Array Tok) : List Nat :=
  let n := toks.size
  let rec scanBody (i : Nat) (found : Bool) : Bool × Nat :=
    if i ≥ n then (found, i)
    else
      match toks.getD i .eof with
      | .rbrace => (found, i + 1)
      | .ident "noreturn" => scanBody (i + 1) true
      | _ => scanBody (i + 1) found
  termination_by n - i
  let rec go (i : Nat) (acc : List Nat) : List Nat :=
    if i + 3 ≥ n then acc
    else
      match toks.getD i .eof, toks.getD (i + 1) .eof, toks.getD (i + 2) .eof, toks.getD (i + 3) .eof with
      | .ident "attributes", .attrGrp grp, .eq, .lbrace =>
        let (hasNR, nextI) := scanBody (i + 4) false
        let acc' := if hasNR then grp :: acc else acc
        if nextI > i then go nextI acc' else acc'
      | _, _, _, _ => go (i + 1) acc
  termination_by n - i
  go 0 []

/-- Pre-scan `attributes #N = { ... denormal_fpenv(...) ... }` (LLVM prints function attributes
through groups). -/
private def prescanDenormGroups (toks : Array Tok) : List (Nat × Option DenormalMode × Option DenormalMode) :=
  let n := toks.size
  -- tokens of the parenthesized group starting after `denormal_fpenv (` at `i`
  let rec inner (i : Nat) (acc : List Tok) : List Tok × Nat :=
    if i ≥ n then (acc.reverse, i)
    else match toks.getD i .eof with
      | .rparen => (acc.reverse, i + 1)
      | t => inner (i + 1) (t :: acc)
  termination_by n - i
  let rec scanBody (i : Nat) (found : Option (Option DenormalMode × Option DenormalMode)) :
      Option (Option DenormalMode × Option DenormalMode) × Nat :=
    if i ≥ n then (found, i)
    else
      match toks.getD i .eof, toks.getD (i + 1) .eof with
      | .rbrace, _ => (found, i + 1)
      | .ident "denormal_fpenv", .lparen =>
        let (ts, j) := inner (i + 2) []
        if j > i then scanBody j (some (denormFromToks ts)) else (found, n)
      | _, _ => scanBody (i + 1) found
  termination_by n - i
  let rec go (i : Nat) (acc : List (Nat × Option DenormalMode × Option DenormalMode)) :=
    if i + 3 ≥ n then acc
    else
      match toks.getD i .eof, toks.getD (i + 1) .eof, toks.getD (i + 2) .eof, toks.getD (i + 3) .eof with
      | .ident "attributes", .attrGrp grp, .eq, .lbrace =>
        let (d?, nextI) := scanBody (i + 4) none
        let acc' := match d? with | some (g, f) => (grp, g, f) :: acc | none => acc
        if nextI > i then go nextI acc' else acc'
      | _, _, _, _ => go (i + 1) acc
  termination_by n - i
  go 0 []

/-- Locate the parameter list of a function header in `[lo, hi)`: the token range strictly inside
the first top-level parenthesis pair following the function's `@name`. -/
def findParamRange (toks : Array Tok) (lo hi : Nat) : Nat × Nat := Id.run do
  let mut i := lo
  while i < hi do
    match toks.getD i .eof with
    | .globalId _ =>
      if toks.getD (i + 1) .eof == .lparen then
        let start := i + 2
        let mut depth : Nat := 1
        let mut j := start
        while j < hi && depth > 0 do
          match toks.getD j .eof with
          | .lparen => depth := depth + 1
          | .rparen => depth := depth - 1
          | _ => pure ()
          j := j + 1
        return (start, if depth == 0 then j - 1 else j)
      i := i + 1
    | _ => i := i + 1
  return (hi, hi)

/-- Parse an entire LLVM IR `.ll` text module into `ParsedModule`. -/
def parseLlvmModule (input : String) (vscale : Nat := 4) : Except String ParsedModule := do
  let (toks, lines) := tokenizeWithLines input
  let fuel := toks.size * 4 + 64
  let initSt : PState := {
    toks := toks
    lines := lines
    rangeMeta := prescanRangeMetadata toks
    intMeta := prescanIntMetadata toks
    noReturnGrps := prescanNoReturnGroups toks
    denormGrps := prescanDenormGroups toks
    vscale := vscale
  }
  let run : ParseM ParsedModule := do
    let mut entities : List TopLevelEntity := []
    let mut dl : DataLayout := .default64LE
    let mut guard := fuel
    while (← peek) != .eof && guard > 0 do
      guard := guard - 1
      match ← peek with
      | .ident "target" =>
        let _ ← bump
        match ← bump with
        | .ident "datalayout" =>
          expect .eq "target datalayout"
          match ← bump with
          | .strLit s =>
            let prevTriple := dl.targetTriple
            dl := { parseDataLayoutString s with targetTriple := prevTriple }
          | t => throw s!"parse error: expected datalayout string, got {repr t}"
        | .ident "triple" =>
          expect .eq "target triple"
          match ← bump with
          | .strLit s => dl := { dl with targetTriple := s }
          | _ => pure ()
        | t => throw s!"parse error: unexpected target directive {repr t}"
      | .ident "source_filename" | .ident "module" =>
        let _ ← bump
        if ← tryEat .eq then let _ ← bump
        else
          -- `module asm "..."`
          let _ ← bump; let _ ← bump
      | .ident "attributes" =>
        let _ ← bump
        let _ ← bump -- `#N`
        expect .eq "attributes"
        expect .lbrace "attributes"
        let mut depth : Nat := 1
        let mut g := fuel
        while depth > 0 && g > 0 do
          g := g - 1
          match ← bump with
          | .lbrace => depth := depth + 1
          | .rbrace => depth := depth - 1
          | .eof => depth := 0
          | _ => pure ()
      | .metaId _ =>
        -- Top-level metadata definition `!N = !{ ... }` or `!named = !{ ... }`
        let _ ← bump
        expect .eq "metadata def"
        let _ ← tryEatIdent "distinct"
        let _ ← tryEat .bang
        if ← tryEat .lbrace then
          let mut depth : Nat := 1
          let mut g := fuel
          while depth > 0 && g > 0 do
            g := g - 1
            match ← bump with
            | .lbrace => depth := depth + 1
            | .rbrace => depth := depth - 1
            | .eof => depth := 0
            | _ => pure ()
        else
          -- `!N = !DI...(...)`
          let _ ← bump
          skipParenGroup fuel
      | .localId typeName =>
        let _ ← bump
        expect .eq "typeDef"
        expectIdent "type" "typeDef"
        if ← tryEatIdent "opaque" then
          entities := .typeDef typeName (.struct false []) :: entities
        else
          let st0 ← get
          set { st0 with vscale := 1 }
          let tyMin ← parseType fuel
          modify fun st => { st with pos := st0.pos, vscale := st0.vscale }
          let ty ← parseType fuel
          modify fun st => { st with typeDefs := (typeName, ty, tyMin) :: st.typeDefs }
          entities := .typeDef typeName ty :: entities
      | .globalId gName =>
        let _ ← bump
        expect .eq "global"
        skipLinkageAndCC
        let mut addrSpace : Nat := 0
        if ← tryEatIdent "addrspace" then
          expect .lparen "global addrspace"
          addrSpace ← parseNatTok "global addrspace"
          expect .rparen "global addrspace"
        let isConst ←
          match ← bump with
          | .ident "constant" => pure true
          | .ident "global" => pure false
          | t => throw s!"parse error: expected 'global' or 'constant', got {repr t}"
        let ty ← parseType fuel
        let initExp? ←
          match (← peek), (← peekAt 1) with
          | .comma, _ | .eof, _ | .ident "define", _ | .ident "declare", _
          | .ident "attributes", _ | .metaId _, _
          | .globalId _, .eq | .localId _, .eq => pure none
          | _, _ => pure (some (← parseExp fuel))
        let mut align? : Option Nat := none
        let mut g2 := 8
        while (← tryEat .comma) && g2 > 0 do
          g2 := g2 - 1
          match ← peek with
          | .ident "align" =>
            let _ ← bump
            align? := some (← parseNatTok "global align")
          | .ident "section" | .ident "comdat" =>
            let _ ← bump; let _ ← bump
          | _ => g2 := 0
        entities := .global {
          name := gName
          ty := ty
          isConstant := isConst
          initializer := initExp?
          align := align?
          addrSpace := addrSpace
        } :: entities
      | .ident "declare" =>
        let _ ← bump
        let (decl, _) ← parseFnHeader fuel
        entities := .declaration decl :: entities
      | .ident "define" =>
        let _ ← bump
        let hdrStart := (← get).pos
        let (decl, argNames) ← parseFnHeader fuel
        let hdrEnd := (← get).pos
        modify fun st => { st with curSrc := #[] }
        expect .lbrace "define body"
        -- Unnamed values continue after the unnamed parameters (named ones take no slot).
        modify fun st => { st with nextAnon := argNames.countP (fun | .anonymous _ => true | _ => false) }
        let mut blocks : List Block := []
        let mut first := true
        let mut g := fuel
        while !(← tryEat .rbrace) && g > 0 do
          g := g - 1
          let blk ← parseBlock fuel first
          first := false
          blocks := blk :: blocks
        let defn : Definition := {
          prototype := decl
          args := argNames
          blocks := blocks.reverse
        }
        let toksNow := (← get).toks
        let (ps, pe) := findParamRange toksNow hdrStart hdrEnd
        modify fun st => { st with
          fnSrcs := st.fnSrcs.push { name := decl.name, paramsStart := ps, paramsEnd := pe, entries := st.curSrc }
          curSrc := #[] }
        entities := .definition defn :: entities
      | tok => throw s!"parse error: unexpected top-level token {repr tok}"
    return { topLevel := { entities := entities.reverse }, dataLayout := dl }
  match run.run initSt with
  | .ok (res, st) => .ok { res with tokens := toks, fnSrcs := st.fnSrcs }
  | .error msg => .error msg

end LeanNanoLlvm.AST.Parser
