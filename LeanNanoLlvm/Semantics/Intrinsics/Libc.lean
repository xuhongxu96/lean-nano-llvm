import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.Semantics.Operations
import LeanNanoLlvm.Util.Text
import LeanNanoLlvm.Util.CFormat
import LeanNanoLlvm.Semantics.Intrinsics.MemTransfer

/-!
# C library calls

`printf`, `puts`, `putchar`, `strlen`, `abort`, `exit` and the other non-allocating libcalls that
`llubi` implements, including C-format rendering of `printf` arguments.
-/

namespace LeanNanoLlvm.Semantics

open AST
open RegisterValue (poisonOf)

/-- Decode a concrete `MemByte` into a `Nat` in `0..255`, returning `none` if any bit is poison/undef. -/
private def memByteToConcreteNat? (mb : MemByte) : Option Nat :=
  match mb.b0, mb.b1, mb.b2, mb.b3, mb.b4, mb.b5, mb.b6, mb.b7 with
  | .concrete k0 _, .concrete k1 _, .concrete k2 _, .concrete k3 _,
    .concrete k4 _, .concrete k5 _, .concrete k6 _, .concrete k7 _ =>
    let b (k : Bool) (sh : Nat) : Nat := if k then (1 <<< sh) else 0
    some (b k0 0 + b k1 1 + b k2 2 + b k3 3 + b k4 4 + b k5 5 + b k6 6 + b k7 7)
  | _, _, _, _, _, _, _, _ => none

/-- Read a null-terminated C string from memory, raising Immediate UB on invalid/OOB/uninit/poison reads. -/
def readCStringPure (mem : MemoryState) (p : Pointer) : Except ExecError String :=
  match mem.resolveObject? p with
  | none => .error (.immediateUB "Invalid memory access via a pointer with nullary provenance")
  | some mo =>
    if mo.state == .freed || mo.state == .dead then
      .error (.immediateUB s!"Use-after-free while reading C-string from '{mo.name}'")
    else if p.addr.toNat < mo.baseAddr || p.addr.toNat ≥ mo.baseAddr + mo.size then
      .error (.immediateUB s!"Out-of-bounds read while parsing C-string in '{mo.name}'")
    else
      let startOff := p.addr.toNat - mo.baseAddr
      let maxFuel := mo.size - startOff
      let rec go (off : Nat) (fuel : Nat) (acc : List Char) : Except ExecError String :=
        match fuel with
        | 0 => .error (.immediateUB "Out-of-bounds read while parsing C-string (missing null terminator)")
        | fuel' + 1 =>
          match memByteToConcreteNat? (mo.bytes.getD off MemByte.poison) with
          | none => .error (.immediateUB s!"Read uninitialized or poison memory while parsing C-string at offset {off - startOff}")
          | some 0 => .ok (String.ofList acc.reverse)
          | some byte => go (off + 1) fuel' (Char.ofNat byte :: acc)
      go startOff maxFuel []

/-- Parse a `printf` conversion's flag/width characters (`llubi` accepts `-= #0123456789`). -/
def parsePrintfChunk (chunk : List Char) : CFormat.Spec :=
  let rec go (sp : CFormat.Spec) (inWidth : Bool) : List Char → CFormat.Spec
    | [] => sp
    | c :: cs =>
      if c.isDigit && (inWidth || c != '0') then
        go { sp with width := sp.width * 10 + (c.toNat - '0'.toNat) } true cs
      else if c == '-' then go { sp with leftAlign := true } inWidth cs
      else if c == ' ' then go { sp with space := true } inWidth cs
      else if c == '#' then go { sp with alt := true } inWidth cs
      else if c == '0' then go { sp with zeroPad := true } inWidth cs
      else go sp inWidth cs
  go {} false chunk

/-- Parse and handle a single `%...` format specifier in `printf` (mirrors `llubi`'s
`Library::executePrintf`), returning `(remainingChars, remainingArgs, optionalWritePatch,
formattedText)`. `argPos` is the (1-based) position of the next variadic argument. -/
def evalPrintfSpec (dl : DataLayout) (rest : List Char) (args : List RegisterValue)
    (mem : MemoryState) (written : Nat) (argPos : Nat) :
    Except ExecError (List Char × List RegisterValue × Option (AllocId × Nat × Array MemByte) × String) :=
  let chunk := rest.takeWhile (fun c => "-= #0123456789".contains c)
  let cs1 := rest.dropWhile (fun c => "-= #0123456789".contains c)
  let cs2 := cs1.dropWhile (fun c => "hljzt".contains c)
  let sp := parsePrintfChunk chunk
  match cs2 with
  | [] => .error (.immediateUB "Invalid format string in printf: missing conversion specifier.")
  | spec :: tail =>
    match args with
    | [] => .error (.immediateUB s!"Not enough arguments provided for the format string. Required argument for '{spec}'.")
    | arg :: restArgs =>
      let isPoison := match arg with
        | .bv _ .poison | .float _ .poison | .ptr _ .poison => true
        | _ => false
      if isPoison then
        .error (.immediateUB s!"Poison argument passed to printf for format specifier '{spec}' at argument index {argPos + 1}.")
      else
        let mismatch :=
          ("diuoxXc".contains spec && !(match arg with | .bv w _ => w == 32 || w == 64 | _ => false)) ||
          ("fFeEgGaA".contains spec && !(match arg with | .float .double _ => true | _ => false)) ||
          ("nps".contains spec && !(match arg with | .ptr _ (.value p) => p.addrWidth ≤ 64 | _ => false))
        if mismatch then
          .error (.immediateUB s!"Argument type mismatch in printf for format specifier '{spec}' at argument index {argPos}.")
        else
          match spec, arg with
          | 'd', .bv _ (.value bv) | 'i', .bv _ (.value bv) =>
            .ok (tail, restArgs, none, CFormat.fmtSigned sp bv.toInt)
          | 'u', .bv _ (.value bv) | 'o', .bv _ (.value bv) | 'x', .bv _ (.value bv)
          | 'X', .bv _ (.value bv) =>
            .ok (tail, restArgs, none, CFormat.fmtUnsigned sp spec bv.toNat)
          | 'c', .bv _ (.value bv) =>
            .ok (tail, restArgs, none, CFormat.pad sp "" (String.singleton (Char.ofNat (bv.toNat % 256))) false)
          | 'f', .float .double (.value flt) | 'F', .float .double (.value flt)
          | 'e', .float .double (.value flt) | 'E', .float .double (.value flt)
          | 'g', .float .double (.value flt) | 'G', .float .double (.value flt)
          | 'a', .float .double (.value flt) | 'A', .float .double (.value flt) =>
            .ok (tail, restArgs, none, CFormat.fmtDouble sp spec flt)
          | 'p', .ptr _ (.value p) =>
            .ok (tail, restArgs, none, "0x" ++ CFormat.fmtUnsigned sp 'x' p.addr.toNat)
          | 's', .ptr _ (.value p) =>
            match readCStringPure mem p with
            | .error e => .error e
            | .ok str => .ok (tail, restArgs, none, CFormat.pad sp "" str false)
          | 'n', .ptr _ (.value p) =>
            match mem.verifyMemAccess p 4 4 true with
            | .error e => .error e
            | .ok (mo, off) =>
              let bytes := valueToBytes dl .modern (.bv 32 (.value (BitVec.ofNat 32 written))) (.int 32)
              .ok (tail, restArgs, some (mo.allocId, off, bytes), "")
          | _, _ => .error (.immediateUB s!"Unknown or unsupported format specifier '{spec}' in printf.")

/-- Format-string interpreter for C `printf` (fuel-bounded over format length). -/
def evalPrintfLoop (dl : DataLayout) (nArgs : Nat) :
    Nat → List Char → List RegisterValue → MemoryState → Nat → Except ExecError (Nat × MemoryState)
  | 0, _, _, mem, written => .ok (written, mem)
  | _ + 1, [], _, mem, written => .ok (written, mem)
  | fuel + 1, '%' :: '%' :: rest, args, mem, written =>
    evalPrintfLoop dl nArgs fuel rest args mem (written + 1)
  | fuel + 1, '%' :: rest, args, mem, written =>
    match evalPrintfSpec dl rest args mem written (nArgs - args.length + 1) with
    | .error e => .error e
    | .ok (tail, restArgs, patch?, piece) =>
      let mem' := match patch? with
        | none => mem
        | some (aid, off, bytes) => mem.writeObjectBytes aid off bytes
      evalPrintfLoop dl nArgs fuel tail restArgs mem' (written + piece.length)
  | fuel + 1, _ :: rest, args, mem, written =>
    evalPrintfLoop dl nArgs fuel rest args mem (written + 1)

theorem evalPrintfLoop_preserves_wf {dl nArgs fuel cs args mem written n mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : evalPrintfLoop dl nArgs fuel cs args mem written = .ok (n, mem')) :
    MemoryState.WellFormed mem' := by
  induction fuel generalizing cs args mem written with
  | zero => unfold evalPrintfLoop at h; cases h; exact hwf
  | succ fuel ih =>
    unfold evalPrintfLoop at h
    split at h
    · cases h; exact hwf
    · cases h; exact hwf
    · rename_i _ _ _ _ _ _ _ _ _ heq; cases heq; exact ih hwf h
    · rename_i _ _ _ _ _ _ _ _ _ heq; cases heq
      cases hs : evalPrintfSpec dl _ _ _ _ _ with
      | error e => rw [hs] at h; cases h
      | ok p =>
        rw [hs] at h; obtain ⟨t, ra, patch?, w1⟩ := p; dsimp only at h
        cases patch? with
        | none => exact ih hwf h
        | some w => exact ih (MemoryState.writeObjectBytes_preserves_wf hwf w.1 w.2.1 w.2.2) h
    · rename_i _ _ _ _ _ _ _ _ _ _ _ _ heq; cases heq; exact ih hwf h

/-- Render the text `printf` writes (executable companion of `evalPrintfLoop`, used by frontends
that need the program's actual output). Returns `none` if formatting raises an error. -/
def renderPrintf (dl : DataLayout) (nArgs : Nat) :
    Nat → List Char → List RegisterValue → MemoryState → String → Option String
  | 0, _, _, _, out => some out
  | _ + 1, [], _, _, out => some out
  | fuel + 1, '%' :: '%' :: rest, args, mem, out => renderPrintf dl nArgs fuel rest args mem (out.push '%')
  | fuel + 1, '%' :: rest, args, mem, out =>
    match evalPrintfSpec dl rest args mem out.length (nArgs - args.length + 1) with
    | .error _ => none
    | .ok (tail, restArgs, patch?, piece) =>
      let mem' := match patch? with
        | none => mem
        | some (aid, off, bytes) => mem.writeObjectBytes aid off bytes
      renderPrintf dl nArgs fuel tail restArgs mem' (out ++ piece)
  | fuel + 1, c :: rest, args, mem, out => renderPrintf dl nArgs fuel rest args mem (out.push c)

/-- Non-allocating C/C++ standard library calls (`free`, `_ZdlPv`, `memcpy`, `memmove`, `memset`, `puts`, `putchar`, `printf`, `exit`, `abort`, `_ZSt9terminatev`). -/
def evalNonAllocLibcall? (dl : DataLayout) (mem : MemoryState)
    (name : String) (argVals : List RegisterValue) :
    Option (Except ExecError (RegisterValue × MemoryState)) :=
  if name == "free" || name == "_ZdlPv" || name == "_ZdaPv" || name == "_ZdlPvm" || name == "_ZdaPvm" then
    some <| match argVals with
      | .ptr _ .poison :: _ => .error (.immediateUB "Poison argument passed to a library call at argument index 0.")
      | .ptr as (.value p) :: _ =>
        if p.isNull dl as then .ok (.void, mem)
        else match mem.resolveObject? p with
          | none => .error (.immediateUB "freeing a pointer with nullary provenance.")
          | some mo =>
            if p.addr.toNat != mo.baseAddr then
              .error (.immediateUB s!"freeing a pointer that does not point to the start of an allocation. Pointer address: 0x{Hex.upper p.addr.toNat}, allocation base: 0x{Hex.upper mo.baseAddr}.")
            else if mo.state == .freed then
              .error (.immediateUB s!"double-freeing a memory object allocated at 0x{Hex.upper mo.baseAddr}.")
            else if !mo.isHeap then
              .error (.immediateUB s!"freeing a non-heap allocation at 0x{Hex.upper mo.baseAddr}.")
            else
              .ok (.void, mem.freeObject mo.allocId)
      | _ => .error (.staticError "free/delete expects pointer argument")
  else if name == "memcpy" then
    some <| match argVals with
      | [dst, src, len] => (execMemTransferPure mem dst src len false true).map (fun m' => (dst, m'))
      | _ => .error (.staticError "memcpy expects 3 arguments")
  else if name == "memmove" then
    some <| match argVals with
      | [dst, src, len] => (execMemTransferPure mem dst src len true true).map (fun m' => (dst, m'))
      | _ => .error (.staticError "memmove expects 3 arguments")
  else if name == "memset" then
    some <| match argVals with
      | [dst, val, len] => (execMemSetPure mem dst val len).map (fun m' => (dst, m'))
      | _ => .error (.staticError "memset expects 3 arguments")
  else if name == "puts" then
    some <| match argVals with
      | [.ptr _ .poison] => .error (.immediateUB "Poison argument passed to a library call at argument index 0")
      | [.ptr _ (.value p)] =>
        match readCStringPure mem p with
        | .error e => .error e
        | .ok _ => .ok (.bv 32 (.value (BitVec.ofNat 32 1)), mem)
      | _ => .error (.staticError "puts expects 1 pointer argument")
  else if name == "putchar" then
    some <| match argVals with
      | [.bv _ .poison] => .error (.immediateUB "Poison argument passed to putchar")
      | [.bv _ (.value bv)] => .ok (.bv 32 (.value (BitVec.ofNat 32 (bv.toNat % 256))), mem)
      | _ => .error (.staticError "putchar expects 1 integer argument")
  else if name == "printf" then
    some <| match argVals with
      | .ptr _ .poison :: _ => .error (.immediateUB "Poison argument passed to a library call at argument index 0")
      | .ptr _ (.value fmtPtr) :: restArgs =>
        match readCStringPure mem fmtPtr with
        | .error e => .error e
        | .ok fmtStr =>
          match evalPrintfLoop dl restArgs.length fmtStr.length fmtStr.toList restArgs mem 0 with
          | .error e => .error e
          | .ok (written, mem') => .ok (.bv 32 (.value (BitVec.ofNat 32 written)), mem')
      | _ => .error (.staticError "printf expects at least 1 pointer argument")
  else if name == "exit" then
    some <| match argVals with
      | [.bv _ .poison] => .error (.immediateUB "Poison argument passed to exit")
      | [.bv _ (.value bv)] => .error (.staticError s!"Program exited with code {bv.toInt}")
      | _ => .error (.staticError "exit expects 1 integer argument")
  else if name == "abort" then
    some (.error (.staticError "Program aborted."))
  else if name == "_ZSt9terminatev" then
    some (.error (.staticError "Program terminated."))
  else
    none

theorem evalNonAllocLibcall?_preserves_wf {dl mem name argVals res mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : evalNonAllocLibcall? dl mem name argVals = some (.ok (res, mem'))) :
    MemoryState.WellFormed mem' := by
  unfold evalNonAllocLibcall? at h
  split at h
  · match argVals, h with
    | .ptr _ .poison :: _, h => cases h
    | .ptr as (.value p) :: _, h =>
      dsimp only at h
      split at h
      · cases h; exact hwf
      · cases hres : mem.resolveObject? p with
        | none => rw [hres] at h; cases h
        | some mo =>
          rw [hres] at h; dsimp only at h
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · cases h; exact MemoryState.freeObject_preserves_wf hwf mo.allocId
  · split at h
    · match argVals, h with
      | [dst, src, len], h =>
        dsimp only at h
        cases ht : execMemTransferPure mem dst src len false true with
        | error e => rw [ht] at h; cases h
        | ok m1 => rw [ht] at h; cases h; exact execMemTransferPure_preserves_wf hwf ht
    · split at h
      · match argVals, h with
        | [dst, src, len], h =>
          dsimp only at h
          cases ht : execMemTransferPure mem dst src len true true with
          | error e => rw [ht] at h; cases h
          | ok m1 => rw [ht] at h; cases h; exact execMemTransferPure_preserves_wf hwf ht
      · split at h
        · match argVals, h with
          | [dst, val, len], h =>
            dsimp only at h
            cases ht : execMemSetPure mem dst val len with
            | error e => rw [ht] at h; cases h
            | ok m1 => rw [ht] at h; cases h; exact execMemSetPure_preserves_wf hwf ht
        · split at h
          · split at h
            · cases h
            · cases hr : readCStringPure mem _ with
              | error e => rw [hr] at h; cases h
              | ok s => rw [hr] at h; cases h; exact hwf
            · cases h
          · split at h
            · split at h
              · cases h
              · cases h; exact hwf
              · cases h
            · split at h
              · split at h
                · cases h
                · cases hr : readCStringPure mem _ with
                  | error e => rw [hr] at h; cases h
                  | ok fmtStr =>
                    rw [hr] at h; dsimp only at h
                    cases hp : evalPrintfLoop dl _ fmtStr.length fmtStr.toList _ mem 0 with
                    | error e => rw [hp] at h; cases h
                    | ok p =>
                      rw [hp] at h; cases h
                      exact evalPrintfLoop_preserves_wf hwf hp
                · cases h
              · split at h
                · split at h <;> cases h
                · split at h
                  · cases h
                  · split at h
                    · cases h
                    · cases h

end LeanNanoLlvm.Semantics
