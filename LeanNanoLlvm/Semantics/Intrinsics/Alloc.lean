import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.Semantics.Operations
import LeanNanoLlvm.Util.Text

/-!
# Allocation libcalls

`malloc`, `calloc`, `realloc`, `aligned_alloc` and C++ `operator new`: a relational
specification (`AllocLibcallSpec`) and the executable `execAllocLibcall` proven to satisfy it.
-/

namespace LeanNanoLlvm.Semantics

open AST
open RegisterValue (poisonOf)

/-- Predicate identifying C++ `operator new` / `operator new[]` mangled names. -/
def isCxxNew (name : String) : Bool :=
  name == "_Znwm" || name == "_Znam" || name == "_Znwj" || name == "_Znaj"

/-- Predicate identifying heap-allocating C/C++ library calls handled relationally via `AllocSpec`. -/
def isAllocLibcall (name : String) : Bool :=
  name == "malloc" || name == "calloc" || isCxxNew name

/-- Name `llubi` gives a heap object: the name of the call's result register (empty if unnamed). -/
def heapObjName : InstructionId → String
  | .id (.name s) => s
  | _ => ""

/-- Extract return pointer address space for `malloc`/`calloc` (defaults to 0). -/
@[simp]
def retAddrSpace : LlvmRetType → Nat
  | .ret (.ptr a) => a
  | _ => 0

/-- Heap allocation alignment (`16` when ABI pointer alignment ≥ 8, else `8`). -/
@[simp]
def heapAllocAlign (dl : DataLayout) (as : Nat) : Nat :=
  if dl.getPointerABIAlign as ≥ 8 then 16 else 8

/--
Relational specification for `malloc`, `calloc`, and C++ `operator new` (used in the primary `Step` relation).
Permits any valid aligned disjoint address via `MemoryState.AllocSpec`, or returning `null` / OOM.
-/
inductive AllocLibcallSpec (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (objName : String) :
    String → LlvmRetType → List RegisterValue → Except ExecError (RegisterValue × MemoryState) → Prop where
  | malloc_poison (retTy : LlvmRetType) (w : Nat) :
      AllocLibcallSpec dl cfg mem objName "malloc" retTy [.bv w .poison]
        (.error (.immediateUB "malloc called with poison size"))
  | malloc_ok (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) (obj : MemoryObject) (mem' : MemoryState) :
      MemoryState.AllocSpec mem dl cfg sz.toNat (heapAllocAlign dl (retAddrSpace retTy))
        objName (retAddrSpace retTy) .uninitialized .heap false obj mem' →
      AllocLibcallSpec dl cfg mem objName "malloc" retTy [.bv w (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (MemoryState.derivePointer dl obj)), mem'))
  | malloc_oom (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) :
      AllocLibcallSpec dl cfg mem objName "malloc" retTy [.bv w (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (Pointer.null dl (retAddrSpace retTy))), mem))
  | malloc_bad_size (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) (msg : String) :
      MemoryState.exceedsMaxObjectSize dl sz.toNat (retAddrSpace retTy) = true →
      AllocLibcallSpec dl cfg mem objName "malloc" retTy [.bv w (.value sz)]
        (.error (.immediateUB msg))
  | malloc_bad_args (retTy : LlvmRetType) (args : List RegisterValue) :
      (∀ w v, args ≠ [.bv w v]) →
      AllocLibcallSpec dl cfg mem objName "malloc" retTy args
        (.error (.staticError "malloc expects 1 integer argument"))
  | calloc_ok (retTy : LlvmRetType) (w1 w2 : Nat) (cnt : BitVec w1) (sz : BitVec w2)
      (obj : MemoryObject) (mem' : MemoryState) :
      cnt.toNat * sz.toNat < (1 <<< max w1 w2) →
      MemoryState.AllocSpec mem dl cfg (cnt.toNat * sz.toNat) (heapAllocAlign dl (retAddrSpace retTy))
        objName (retAddrSpace retTy) .zeroed .heap false obj mem' →
      AllocLibcallSpec dl cfg mem objName "calloc" retTy [.bv w1 (.value cnt), .bv w2 (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (MemoryState.derivePointer dl obj)), mem'))
  | calloc_null (retTy : LlvmRetType) (w1 w2 : Nat) (cnt : BitVec w1) (sz : BitVec w2) :
      AllocLibcallSpec dl cfg mem objName "calloc" retTy [.bv w1 (.value cnt), .bv w2 (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (Pointer.null dl (retAddrSpace retTy))), mem))
  | calloc_bad_size (retTy : LlvmRetType) (w1 w2 : Nat) (cnt : BitVec w1) (sz : BitVec w2) (msg : String) :
      cnt.toNat * sz.toNat < (1 <<< max w1 w2) →
      MemoryState.exceedsMaxObjectSize dl (cnt.toNat * sz.toNat) (retAddrSpace retTy) = true →
      AllocLibcallSpec dl cfg mem objName "calloc" retTy [.bv w1 (.value cnt), .bv w2 (.value sz)]
        (.error (.immediateUB msg))
  | calloc_bad_args (retTy : LlvmRetType) (args : List RegisterValue) :
      (∀ w1 w2 c s, args ≠ [.bv w1 (.value c), .bv w2 (.value s)]) →
      AllocLibcallSpec dl cfg mem objName "calloc" retTy args
        (.error (.immediateUB "calloc called with poison/invalid arguments"))
  | cxxNew_poison (name : String) (retTy : LlvmRetType) (w : Nat) :
      isCxxNew name = true →
      AllocLibcallSpec dl cfg mem objName name retTy [.bv w .poison]
        (.error (.immediateUB "operator new called with poison size"))
  | cxxNew_ok (name : String) (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) (obj : MemoryObject) (mem' : MemoryState) :
      isCxxNew name = true →
      MemoryState.AllocSpec mem dl cfg sz.toNat (heapAllocAlign dl (retAddrSpace retTy))
        objName (retAddrSpace retTy) .uninitialized .heap false obj mem' →
      AllocLibcallSpec dl cfg mem objName name retTy [.bv w (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (MemoryState.derivePointer dl obj)), mem'))
  | cxxNew_oom (name : String) (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) :
      isCxxNew name = true →
      AllocLibcallSpec dl cfg mem objName name retTy [.bv w (.value sz)]
        (.error .outOfMemory)
  | cxxNew_bad_args (name : String) (retTy : LlvmRetType) (args : List RegisterValue) :
      isCxxNew name = true →
      (∀ w v, args ≠ [.bv w v]) →
      AllocLibcallSpec dl cfg mem objName name retTy args
        (.error (.staticError "operator new expects 1 integer argument"))

/-- Executable `malloc` / `calloc` / `operator new` implementation using deterministic bump allocation. -/
def execAllocLibcall (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (objName : String) (name : String) (retTy : LlvmRetType) (argVals : List RegisterValue) :
    Option (Except ExecError (RegisterValue × MemoryState)) :=
  if name == "malloc" then
    some <| match argVals with
      | [a] => match a with
        | .bv _ .poison => .error (.immediateUB "malloc called with poison size")
        | .bv _ (.value sz) =>
          let as := retAddrSpace retTy
          let maxAlign := heapAllocAlign dl as
          match mem.allocate dl cfg sz.toNat maxAlign objName as .uninitialized .heap false with
          | .ok (obj, mem') => .ok (.ptr as (.value (MemoryState.derivePointer dl obj)), mem')
          | .error _ => .ok (.ptr as (.value (Pointer.null dl as)), mem)
        | _ => .error (.staticError "malloc expects 1 integer argument")
      | _ => .error (.staticError "malloc expects 1 integer argument")
  else if name == "calloc" then
    some <| match argVals with
      | [a1, a2] => match a1, a2 with
        | .bv w1 (.value cnt), .bv w2 (.value sz) =>
          let as := retAddrSpace retTy
          let maxAlign := heapAllocAlign dl as
          let total := cnt.toNat * sz.toNat
          if total ≥ (1 <<< max w1 w2) then
            .ok (.ptr as (.value (Pointer.null dl as)), mem)
          else
            match mem.allocate dl cfg total maxAlign objName as .zeroed .heap false with
            | .ok (obj, mem') => .ok (.ptr as (.value (MemoryState.derivePointer dl obj)), mem')
            | .error _ => .ok (.ptr as (.value (Pointer.null dl as)), mem)
        | _, _ => .error (.immediateUB "calloc called with poison/invalid arguments")
      | _ => .error (.immediateUB "calloc called with poison/invalid arguments")
  else if isCxxNew name then
    some <| match argVals with
      | [a] => match a with
        | .bv _ .poison => .error (.immediateUB "operator new called with poison size")
        | .bv _ (.value sz) =>
          let as := retAddrSpace retTy
          let maxAlign := heapAllocAlign dl as
          match mem.allocate dl cfg sz.toNat maxAlign objName as .uninitialized .heap false with
          | .ok (obj, mem') => .ok (.ptr as (.value (MemoryState.derivePointer dl obj)), mem')
          | .error _ => .error .outOfMemory
        | _ => .error (.staticError "operator new expects 1 integer argument")
      | _ => .error (.staticError "operator new expects 1 integer argument")
  else
    none

private theorem allocate_error_cases {mem : MemoryState} {dl : DataLayout} {cfg : SemanticsConfig}
    {size align : Nat} {name : String} {as : Nat} {initK : MemInitKind} {allocK : MemAllocKind}
    {isC : Bool} {e : ExecError}
    (h : mem.allocate dl cfg size align name as initK allocK isC = .error e) :
    e = .outOfMemory ∨
    (∃ msg, e = .immediateUB msg ∧ MemoryState.exceedsMaxObjectSize dl size as = true) := by
  cases mem
  unfold MemoryState.allocate at h
  dsimp only at h
  by_cases hsz : MemoryState.exceedsMaxObjectSize dl size as = true
  · rw [if_pos hsz] at h; cases h; exact Or.inr ⟨_, rfl, hsz⟩
  · rw [if_neg hsz] at h
    split at h
    · cases h; exact Or.inl rfl
    · split at h
      · cases h; exact Or.inl rfl
      · cases h

theorem execAllocLibcall_sound {dl cfg mem objName name retTy argVals res}
    (hwf : MemoryState.WellFormed mem)
    (h : execAllocLibcall dl cfg mem objName name retTy argVals = some res) :
    AllocLibcallSpec dl cfg mem objName name retTy argVals res := by
  unfold execAllocLibcall at h
  by_cases hm : (name == "malloc") = true
  · have hnm : name = "malloc" := eq_of_beq hm
    subst hnm
    simp only [hm, ↓reduceIte, Option.some.injEq] at h
    subst h
    cases argVals with
    | cons a rest =>
      cases rest with
      | nil =>
        cases a with
        | bv w v =>
          cases v using PoisonOr.casesOn' with
          | poison => exact AllocLibcallSpec.malloc_poison retTy w
          | value sz =>
            dsimp only
            cases halloc : mem.allocate dl cfg sz.toNat (heapAllocAlign dl (retAddrSpace retTy))
                objName (retAddrSpace retTy) .uninitialized .heap false with
            | ok p =>
              exact AllocLibcallSpec.malloc_ok retTy w sz p.1 p.2
                (MemoryState.allocate_satisfies_AllocSpec hwf halloc)
            | error _ =>
              exact AllocLibcallSpec.malloc_oom retTy w sz
        | _ => exact AllocLibcallSpec.malloc_bad_args retTy _ (by intro w v heq; simp at heq)
      | cons b bs => exact AllocLibcallSpec.malloc_bad_args retTy (a :: b :: bs) (by intro w v heq; cases heq)
    | nil => exact AllocLibcallSpec.malloc_bad_args retTy [] (by intro w v heq; cases heq)
  · have hmf : (name == "malloc") = false := Bool.eq_false_iff.mpr hm
    simp only [hmf, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hc : (name == "calloc") = true
    · have hnm : name = "calloc" := eq_of_beq hc
      subst hnm
      simp only [hc, ↓reduceIte, Option.some.injEq] at h
      subst h
      cases argVals with
      | cons a1 r1 =>
        cases r1 with
        | cons a2 r2 =>
          cases r2 with
          | nil =>
            cases a1 with
            | bv w1 v1 =>
              cases v1 using PoisonOr.casesOn' with
              | value cnt =>
                cases a2 with
                | bv w2 v2 =>
                  cases v2 using PoisonOr.casesOn' with
                  | value sz =>
                    dsimp only
                    by_cases hov : cnt.toNat * sz.toNat ≥ 1 <<< max w1 w2
                    · rw [if_pos hov]
                      exact AllocLibcallSpec.calloc_null retTy w1 w2 cnt sz
                    · rw [if_neg hov]
                      have hlt : cnt.toNat * sz.toNat < 1 <<< max w1 w2 := by omega
                      cases halloc : mem.allocate dl cfg (cnt.toNat * sz.toNat)
                          (heapAllocAlign dl (retAddrSpace retTy))
                          objName (retAddrSpace retTy) .zeroed .heap false with
                      | ok p =>
                        exact AllocLibcallSpec.calloc_ok retTy w1 w2 cnt sz p.1 p.2 hlt
                          (MemoryState.allocate_satisfies_AllocSpec hwf halloc)
                      | error _ =>
                        exact AllocLibcallSpec.calloc_null retTy w1 w2 cnt sz
                  | poison =>
                    exact AllocLibcallSpec.calloc_bad_args retTy _ (by
                      intro _ _ _ _ heq
                      simp only [List.cons.injEq, RegisterValue.bv.injEq, and_true] at heq
                      obtain ⟨_, rfl, hp⟩ := heq
                      exact PoisonOr.poison_ne_value _ (eq_of_heq hp))
                | _ => exact AllocLibcallSpec.calloc_bad_args retTy _ (by intro _ _ _ _ heq; simp at heq)
              | poison =>
                exact AllocLibcallSpec.calloc_bad_args retTy _ (by
                  intro _ _ _ _ heq
                  simp only [List.cons.injEq, RegisterValue.bv.injEq, and_true] at heq
                  obtain ⟨⟨rfl, hp⟩, _⟩ := heq
                  exact PoisonOr.poison_ne_value _ (eq_of_heq hp))
            | _ => exact AllocLibcallSpec.calloc_bad_args retTy _ (by intro _ _ _ _ heq; simp at heq)
          | cons a3 r3 =>
            exact AllocLibcallSpec.calloc_bad_args retTy (a1 :: a2 :: a3 :: r3) (by intro _ _ _ _ heq; cases heq)
        | nil => exact AllocLibcallSpec.calloc_bad_args retTy [a1] (by intro _ _ _ _ heq; cases heq)
      | nil => exact AllocLibcallSpec.calloc_bad_args retTy [] (by intro _ _ _ _ heq; cases heq)
    · have hcf : (name == "calloc") = false := Bool.eq_false_iff.mpr hc
      simp only [hcf, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hn : isCxxNew name = true
      · simp only [hn, ↓reduceIte, Option.some.injEq] at h
        subst h
        cases argVals with
        | cons a rest =>
          cases rest with
          | nil =>
            cases a with
            | bv w v =>
              cases v using PoisonOr.casesOn' with
              | poison => exact AllocLibcallSpec.cxxNew_poison name retTy w hn
              | value sz =>
                dsimp only
                cases halloc : mem.allocate dl cfg sz.toNat (heapAllocAlign dl (retAddrSpace retTy))
                    objName (retAddrSpace retTy) .uninitialized .heap false with
                | ok p =>
                  exact AllocLibcallSpec.cxxNew_ok name retTy w sz p.1 p.2 hn
                    (MemoryState.allocate_satisfies_AllocSpec hwf halloc)
                | error _ =>
                  exact AllocLibcallSpec.cxxNew_oom name retTy w sz hn
            | _ => exact AllocLibcallSpec.cxxNew_bad_args name retTy _ hn (by intro w v heq; simp at heq)
          | cons b bs => exact AllocLibcallSpec.cxxNew_bad_args name retTy (a :: b :: bs) hn (by intro w v heq; cases heq)
        | nil => exact AllocLibcallSpec.cxxNew_bad_args name retTy [] hn (by intro w v heq; cases heq)
      · have hnf : isCxxNew name = false := Bool.eq_false_iff.mpr hn
        simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
        cases h

theorem AllocLibcallSpec.preserves_wf {dl cfg mem objName name retTy argVals retVal mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : AllocLibcallSpec dl cfg mem objName name retTy argVals (.ok (retVal, mem'))) :
    MemoryState.WellFormed mem' := by
  cases h with
  | malloc_ok _ _ _ _ _ hspec => exact hspec.preserves_wf hwf
  | malloc_oom _ _ _ => exact hwf
  | calloc_ok _ _ _ _ _ _ _ _ hspec => exact hspec.preserves_wf hwf
  | calloc_null _ _ _ _ _ => exact hwf
  | cxxNew_ok _ _ _ _ _ _ _ hspec => exact hspec.preserves_wf hwf

end LeanNanoLlvm.Semantics
