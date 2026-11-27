import Lean
import LeanNanoLlvm.Refinement.Refinement

/-!
# Refinement Automation Tactics (`llvm_intro`, `llvm_symexec`, `llvm_vc`, `llvm_refine`)

Kernel-pure, general-purpose automation for LLVM behavioral refinement proofs
(`x ⊒ y`, `x ⊒[cfg] y`, `x ⊒⟨env⟩ y`). All tactics produce standard Lean kernel proof terms
using only `{propext, Classical.choice, Quot.sound}` (no `bv_decide`, `native_decide`, or
`Lean.ofReduceBool`).

## Tactic Pipeline
1. `llvm_intro`   — Unpacks `Definition.IsRefinedBy*`, checks signature compatibility, introduces
                    `initMem` and `args`, destructures `args` for any arity `0..N`, and reduces
                    `initCallConfig` on both source and target to `.running` states.
2. `llvm_symexec` — Dispatches on the head AST constructor of the current instruction/terminator
                    to symbolically execute source and target (`intBinaryOp`, `icmp`, `select`,
                    `conversionOp`, `floatUnaryOp`, `freeze`, `br`, `condBr`, `switch`, `phi`,
                    `ret`, `retVoid`, `unreachable`), short-circuiting on source `.ub` / `CanAbort`
                    and reducing `.halted` vs `.halted` to `RegisterValue.IsRefinedBy .id retX retY`.
3. `llvm_vc`      — Extracts clean, pure Lean verification conditions (`BitVec` / `Bool` / `Float`)
                    by splitting `PoisonOr` cases (auto-closing `.poison ⊒ _`), unfolding pure LLVM
                    evaluators and flag guards, and closing trivial reflexive/contradictory branches.
4. `llvm_refine`  — Composes `llvm_intro; llvm_symexec; llvm_vc` and attempts standard Lean
                    closers (`rfl`, `trivial`, `contradiction`, `grind`, `bv_omega`,
                    `ext _ _; simp; grind`); any remaining pure VC is left exposed for an explicit
                    Lean proof.
-/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### 1. Argument Well-Formedness Destructuring Lemmas -/

theorem RegisterValue.wellFormedFor_int_iff {w : Nat} {v : RegisterValue} :
    RegisterValue.WellFormedFor (.int w) v ↔ ∃ x : PoisonOr (BitVec w), v = .bv w x := by
  constructor
  · cases v with
    | bv w' x =>
      intro h
      simp only [RegisterValue.WellFormedFor] at h
      subst h
      exact ⟨x, rfl⟩
    | _ => simp [RegisterValue.WellFormedFor]
  · rintro ⟨x, rfl⟩
    rfl

theorem RegisterValue.wellFormedFor_float_iff {ft : AST.FloatType} {v : RegisterValue} :
    RegisterValue.WellFormedFor (.float ft) v ↔ ∃ x : FloatW ft, v = .float ft x := by
  constructor
  · cases v with
    | float ft' x =>
      intro h
      simp only [RegisterValue.WellFormedFor] at h
      subst h
      exact ⟨x, rfl⟩
    | _ => simp [RegisterValue.WellFormedFor]
  · rintro ⟨x, rfl⟩
    rfl

theorem RegisterValue.wellFormedFor_ptr_iff {as : Nat} {v : RegisterValue} :
    RegisterValue.WellFormedFor (.ptr as) v ↔ ∃ x : PoisonOr Pointer, v = .ptr as x := by
  constructor
  · cases v with
    | ptr as' x =>
      intro h
      simp only [RegisterValue.WellFormedFor] at h
      subst h
      exact ⟨x, rfl⟩
    | _ => simp [RegisterValue.WellFormedFor]
  · rintro ⟨x, rfl⟩
    rfl

theorem RegisterValue.wellFormedForList_nil_iff {vs : List RegisterValue} :
    RegisterValue.WellFormedForList [] vs ↔ vs = [] := by
  cases vs <;> simp [RegisterValue.WellFormedForList]

theorem RegisterValue.wellFormedForList_cons_iff {t : AST.LlvmType} {ts : List AST.LlvmType}
    {vs : List RegisterValue} :
    RegisterValue.WellFormedForList (t :: ts) vs ↔
      ∃ v rest, vs = v :: rest ∧ RegisterValue.WellFormedFor t v ∧
        RegisterValue.WellFormedForList ts rest := by
  cases vs with
  | nil => simp [RegisterValue.WellFormedForList]
  | cons v rest =>
    simp only [RegisterValue.WellFormedForList, List.cons.injEq]
    constructor
    · intro ⟨hv, hrest⟩; exact ⟨v, rest, ⟨rfl, rfl⟩, hv, hrest⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, hv, hrest⟩; exact ⟨hv, hrest⟩

/-! ### 2. Semantic Bridges (Refinement, Pure Evaluators & Constant Normalization) -/

theorem Config.IsRefinedBy.of_unreachable_left {callerIds : List AllocId}
    {st : MachineState} {frame : CallFrame} {callers : List CallFrame} {tid : AST.InstructionId}
    {cY : Config}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .unreachable)) :
    Config.IsRefinedBy callerIds (.running st) cY :=
  Config.IsRefinedBy.of_canAbort
    (Or.inl ⟨[], "Reached unreachable instruction",
      StarStep.single (Step.term hf hc hterm StepTerm.unreachable_ub)⟩)

theorem Step.br_det {st frame callers tid dest nextBlk phis body ups}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .br dest))
    (hfind : frame.defn.findBlock? dest = some nextBlk)
    (hsplit : splitPhis nextBlk.code = (phis, body))
    (hphis : ∀ res, EvalPhis st.dataLayout st.config frame.registers frame.curBlock st.memory phis res ↔
      res = .ok (ups, st.memory)) :
    Step (.running st) none (.running (st.withFramesAndMemory
      (frame.jumpTo nextBlk.id body nextBlk.terminator (commitPhiUpdates frame.registers ups) :: callers)
      st.memory)) :=
  (Step.br_det_iff hf hc hterm hfind hsplit hphis none _).mpr ⟨rfl, rfl⟩

theorem Step.condBr_val_det {st frame callers tid condExp tDest fDest b nextBlk phis body ups}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .condBr condExp tDest fDest))
    (hcond : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory .i1 condExp =
      some (.ok (.bv 1 (.value b))))
    (hfind : frame.defn.findBlock? (if b != 0 then tDest else fDest) = some nextBlk)
    (hsplit : splitPhis nextBlk.code = (phis, body))
    (hphis : ∀ res, EvalPhis st.dataLayout st.config frame.registers frame.curBlock st.memory phis res ↔
      res = .ok (ups, st.memory)) :
    Step (.running st) none (.running (st.withFramesAndMemory
      (frame.jumpTo nextBlk.id body nextBlk.terminator (commitPhiUpdates frame.registers ups) :: callers)
      st.memory)) :=
  (Step.condBr_val_det_iff hf hc hterm hcond hfind hsplit hphis none _).mpr ⟨rfl, rfl⟩

theorem Step.switch_val_det {st frame callers tid ty condExp defDest cases w bv nextBlk phis body ups}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .switch ty condExp defDest cases))
    (hcond : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty condExp =
      some (.ok (.bv w (.value bv))))
    (hfind : frame.defn.findBlock?
      (match cases.find? (fun (cv, _) => BitVec.ofInt w cv == bv) with
       | some (_, lbl) => lbl
       | none => defDest) = some nextBlk)
    (hsplit : splitPhis nextBlk.code = (phis, body))
    (hphis : ∀ res, EvalPhis st.dataLayout st.config frame.registers frame.curBlock st.memory phis res ↔
      res = .ok (ups, st.memory)) :
    Step (.running st) none (.running (st.withFramesAndMemory
      (frame.jumpTo nextBlk.id body nextBlk.terminator (commitPhiUpdates frame.registers ups) :: callers)
      st.memory)) :=
  (Step.switch_val_det_iff hf hc hterm hcond hfind hsplit hphis none _).mpr ⟨rfl, rfl⟩

theorem Step.freeze_bv_val {st frame callers tid ty e rest w b}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (tid, .freeze (ty, e)) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e =
      some (.ok (.bv w (.value b)))) :
    Step (.running st) none (finishRegInstr st frame callers rest tid (.bv w (.value b)) st.memory) :=
  (Step.freeze_bv_val_iff hf hc h1 none _).mpr ⟨rfl, rfl⟩

theorem Step.freeze_bv_poison_zero {st frame callers iid ty e rest w}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .freeze (ty, e)) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e =
      some (.ok (.bv w .poison))) :
    Step (.running st) none
      (finishRegInstr st frame callers rest iid (.bv w (.value (BitVec.ofNat w 0))) st.memory) :=
  Step.freeze_bv_poison_step hf hc h1 (BitVec.ofNat w 0) (fun _ => rfl)

theorem Config.IsRefinedBy.of_freeze_poison_right {callerIds : List AllocId}
    {stY : MachineState} {frame : CallFrame} {callers : List CallFrame}
    {iid : AST.InstructionId} {ty : AST.LlvmType} {e : AST.Exp} {rest : AST.Code}
    {w : Nat} {cX : Config}
    (hf : stY.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .freeze (ty, e)) :: rest)
    (h1 : evalPureLeafExp? stY.dataLayout stY.config frame.registers stY.memory ty e =
      some (.ok (.bv w .poison)))
    (hcont : ∀ b : BitVec w, (stY.config.freezeMode = .zero → b = BitVec.ofNat w 0) →
      Config.IsRefinedBy callerIds cX
        (finishRegInstr stY frame callers rest iid (.bv w (.value b)) stY.memory)) :
    Config.IsRefinedBy callerIds cX (.running stY) :=
  Config.IsRefinedBy.of_step_right_forall fun ev cY' hs => by
    obtain ⟨rfl, b, hm, rfl⟩ := Step.freeze_bv_poison_inv hf hc h1 hs
    exact ⟨rfl, hcont b hm⟩

/-- Non-`@[simp]` refinement predicate on `PoisonOr α` so `simp [simp_llvm]` reduces inner
    `IntOps` / `if`-guards before eliminating the refinement relation. -/
def PoisonOr.IsRefinedBy {α : Type} : PoisonOr α → PoisonOr α → Prop
  | .poison, _ => True
  | .value a, .value b => a = b
  | .value _, .poison => False

theorem RegisterValue.isRefinedBy_bv_of_poisonOr {inj : MemoryInjection} {w : Nat}
    {x y : PoisonOr (BitVec w)} (h : PoisonOr.IsRefinedBy x y) :
    RegisterValue.IsRefinedBy inj (.bv w x) (.bv w y) := by
  cases x using PoisonOr.casesOn' <;> cases y using PoisonOr.casesOn'
  · exact rfl
  · exact rfl
  · exact False.elim h
  · exact ⟨rfl, h⟩

@[simp_llvm]
theorem PoisonOr.isRefinedBy_poison {α : Type} {y : PoisonOr α} :
    PoisonOr.IsRefinedBy .poison y := trivial

@[simp_llvm]
theorem PoisonOr.isRefinedBy_value {α : Type} {a b : α} :
    PoisonOr.IsRefinedBy (.value a) (.value b) ↔ a = b := Iff.rfl

@[simp_llvm]
theorem PoisonOr.isRefinedBy_ite_poison {α : Type} {c : Prop} [Decidable c] {x y : PoisonOr α} :
    PoisonOr.IsRefinedBy (if c then .poison else x) y ↔ (¬ c → PoisonOr.IsRefinedBy x y) := by
  by_cases hc : c <;> simp [hc, PoisonOr.IsRefinedBy]

@[simp_llvm]
theorem PoisonOr.isRefinedBy_ite_else_poison {α : Type} {c : Prop} [Decidable c] {x y : PoisonOr α} :
    PoisonOr.IsRefinedBy (if c then x else .poison) y ↔ (c → PoisonOr.IsRefinedBy x y) := by
  by_cases hc : c <;> simp [hc, PoisonOr.IsRefinedBy]

@[simp_llvm]
theorem PoisonOr.isRefinedBy_ite_right {α : Type} {c : Prop} [Decidable c] {x y1 y2 : PoisonOr α} :
    PoisonOr.IsRefinedBy x (if c then y1 else y2) ↔
      (c → PoisonOr.IsRefinedBy x y1) ∧ (¬ c → PoisonOr.IsRefinedBy x y2) := by
  by_cases hc : c <;> simp [hc]

@[simp_llvm high, simp high]
theorem RegisterValue.isRefinedBy_bv_poison {inj : MemoryInjection} {w : Nat}
    {y : PoisonOr (BitVec w)} :
    RegisterValue.IsRefinedBy inj (.bv w .poison) (.bv w y) := rfl

@[simp_llvm high, simp high]
theorem RegisterValue.isRefinedBy_bv_value {inj : MemoryInjection} {w : Nat}
    {a b : BitVec w} :
    RegisterValue.IsRefinedBy inj (.bv w (.value a)) (.bv w (.value b)) ↔ a = b := by
  simp [RegisterValue.IsRefinedBy]

@[simp_llvm high, simp high]
theorem RegisterValue.isRefinedBy_float_poison {inj : MemoryInjection} {ft : AST.FloatType}
    {y : FloatW ft} :
    RegisterValue.IsRefinedBy inj (.float ft .poison) (.float ft y) := rfl

@[simp_llvm high, simp high]
theorem RegisterValue.isRefinedBy_float_value {inj : MemoryInjection} {ft : AST.FloatType}
    {a b : IEEEFloat ft.format} :
    RegisterValue.IsRefinedBy inj (.float ft (.value a)) (.float ft (.value b)) ↔ a = b := by
  simp [RegisterValue.IsRefinedBy]

@[simp_llvm high, simp high]
theorem RegisterValue.isRefinedBy_ptr_poison {inj : MemoryInjection} {as : Nat}
    {y : PoisonOr Pointer} :
    RegisterValue.IsRefinedBy inj (.ptr as .poison) (.ptr as y) := rfl

@[simp_llvm high, simp high]
theorem RegisterValue.isRefinedBy_void {inj : MemoryInjection} :
    RegisterValue.IsRefinedBy inj .void .void := trivial

@[simp_llvm, simp_step]
theorem evalSelectPure_bv (c : PoisonOr (BitVec 1)) (w : Nat) (t f : PoisonOr (BitVec w)) :
    evalSelectPure (.bv 1 c) (.bv w t) (.bv w f) =
      .ok (.bv w (match c with | .poison => .poison | .value b => if b != 0 then t else f)) := by
  cases c using PoisonOr.casesOn' with
  | poison => rfl
  | value b =>
    simp only [evalSelectPure]
    split <;> rfl

@[simp_llvm, simp_step]
theorem evalSelectPure_float (c : PoisonOr (BitVec 1)) (ft : AST.FloatType)
    (t f : FloatW ft) :
    evalSelectPure (.bv 1 c) (.float ft t) (.float ft f) =
      .ok (.float ft (match c with | .poison => .poison | .value b => if b != 0 then t else f)) := by
  cases c using PoisonOr.casesOn' with
  | poison => rfl
  | value b =>
    simp only [evalSelectPure]
    split <;> rfl

@[simp_llvm, simp_step]
theorem evalSelectPure_ptr (c : PoisonOr (BitVec 1)) (as : Nat) (t f : PoisonOr Pointer) :
    evalSelectPure (.bv 1 c) (.ptr as t) (.ptr as f) =
      .ok (.ptr as (match c with | .poison => .poison | .value b => if b != 0 then t else f)) := by
  cases c using PoisonOr.casesOn' with
  | poison => rfl
  | value b =>
    simp only [evalSelectPure]
    split <;> rfl

@[simp_llvm, simp_step]
theorem evalConversionExec_trunc (dl : AST.DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (nuw nsw : Bool) (fromW toW : Nat) (iv : PoisonOr (BitVec fromW)) (o : OracleState) :
    evalConversionExec dl cfg mem (.trunc nuw nsw) (.int fromW) (.bv fromW iv) (.int toW) o =
      .ok (.bv toW (trunc toW iv { nuw := nuw, nsw := nsw }), mem, o) := rfl

@[simp_llvm, simp_step]
theorem evalConversionExec_zext (dl : AST.DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (nneg : Bool) (fromW toW : Nat) (iv : PoisonOr (BitVec fromW)) (o : OracleState) :
    evalConversionExec dl cfg mem (.zext nneg) (.int fromW) (.bv fromW iv) (.int toW) o =
      .ok (.bv toW (zext toW iv { nneg := nneg }), mem, o) := rfl

@[simp_llvm, simp_step]
theorem evalConversionExec_sext (dl : AST.DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (fromW toW : Nat) (iv : PoisonOr (BitVec fromW)) (o : OracleState) :
    evalConversionExec dl cfg mem .sext (.int fromW) (.bv fromW iv) (.int toW) o =
      .ok (.bv toW (sext toW iv), mem, o) := rfl

theorem RegisterValue.isRefinedBy_float_of_poisonOr {inj : MemoryInjection} {ft : AST.FloatType}
    {x y : FloatW ft} (h : PoisonOr.IsRefinedBy x y) :
    RegisterValue.IsRefinedBy inj (.float ft x) (.float ft y) := by
  cases x using PoisonOr.casesOn' <;> cases y using PoisonOr.casesOn'
  · exact rfl
  · exact rfl
  · exact False.elim h
  · exact ⟨rfl, h⟩

@[simp_llvm, simp_step]
theorem evalFloatUnaryExec_fneg_no_nsz (fmf : AST.FastMathFlags) (hnsz : fmf.nsz = false)
    (ft : AST.FloatType) (hnp : ft ≠ .ppc_fp128)
    (fw : FloatW ft) (o : OracleState) :
    evalFloatUnaryExec (.fneg fmf) (.float ft) (.float ft fw) o =
      .ok (.float ft (match fw with
        | .poison => .poison
        | .value x =>
          if fmf.nnan && x.isNaN then .poison
          else if fmf.ninf && x.isInf then .poison
          else handleFMF fmf false false x.neg), o) := by
  cases fw using PoisonOr.casesOn' with
  | poison => rfl
  | value x =>
    cases ft <;> try exact absurd rfl hnp
    all_goals
      simp only [evalFloatUnaryExec, evalFloatUnaryOp, fmfIn, hnsz, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : (fmf.nnan && x.isNaN) = true
      · simp only [h1, ↓reduceIte]
      · by_cases h2 : (fmf.ninf && x.isInf) = true
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

@[simp_llvm, simp_step]
theorem evalICmpScalarPure_bv (dl : AST.DataLayout) (ss : Bool) (pred : AST.ICmpPred)
    (w : Nat) (b1 b2 : PoisonOr (BitVec w)) :
    evalICmpScalarPure dl ss pred (.bv w b1) (.bv w b2) =
      .ok (.bv 1 (icmp ss pred b1 b2)) := by
  simp [evalICmpScalarPure]

@[simp_llvm, simp_step]
theorem liftBinaryPure_bv (w1 w2 : Nat) (b1 : PoisonOr (BitVec w1)) (b2 : PoisonOr (BitVec w2))
    (ty : AST.LlvmType) (f : RegisterValue → RegisterValue → Except ExecError RegisterValue) :
    liftBinaryPure ty (.bv w1 b1) (.bv w2 b2) f = f (.bv w1 b1) (.bv w2 b2) := rfl

@[simp_llvm, simp_step]
theorem evalPureLeafExp_bool (dl : AST.DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap AST.Identifier RegisterValue) (mem : MemoryState) (b : Bool) :
    evalPureLeafExp? dl cfg regs mem .i1 (.bool b) =
      some (.ok (.bv 1 (.value (if b then 1#1 else 0#1)))) := by
  cases b <;> rfl

@[simp_llvm, simp_step]
theorem evalPureLeafExp_int (dl : AST.DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap AST.Identifier RegisterValue) (mem : MemoryState) (w : Nat) (n : Int) :
    evalPureLeafExp? dl cfg regs mem (.int w) (.int n) =
      some (.ok (.bv w (.value (BitVec.ofInt w n)))) := rfl

@[simp_llvm, simp_step]
theorem evalPureLeafExp_poison_int (dl : AST.DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap AST.Identifier RegisterValue) (mem : MemoryState) (w : Nat) :
    evalPureLeafExp? dl cfg regs mem (.int w) .poison =
      some (.ok (.bv w .poison)) := rfl

@[simp_llvm, simp_step]
theorem evalPureLeafExp_poison_float (dl : AST.DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap AST.Identifier RegisterValue) (mem : MemoryState) (ft : AST.FloatType) :
    evalPureLeafExp? dl cfg regs mem (.float ft) .poison =
      some (.ok (.float ft .poison)) := rfl

@[simp_llvm, simp_step]
theorem evalPureLeafExp_poison_ptr (dl : AST.DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap AST.Identifier RegisterValue) (mem : MemoryState) (as : Nat) :
    evalPureLeafExp? dl cfg regs mem (.ptr as) .poison =
      some (.ok (.ptr as .poison)) := rfl

/-- Normalize non-negative `BitVec.ofInt` constants to `BitVec.ofNat` so `grind` / `ext` see them uniformly. -/
@[simp_llvm]
theorem bitvec_ofInt_ofNat (w n : Nat) :
    BitVec.ofInt w (Int.ofNat n) = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- Normalize negated `BitVec.ofInt` constants (`-1`, `-2`, ...) to negated `BitVec`. -/
@[simp_llvm]
theorem bitvec_ofInt_neg (w : Nat) (n : Int) :
    BitVec.ofInt w (-n) = -(BitVec.ofInt w n) :=
  BitVec.ofInt_neg

/-- Normalize `Int.negSucc` `BitVec.ofInt` constants (`-1`, `-2`, ...) to negated `BitVec.ofNat`. -/
@[simp_llvm]
theorem bitvec_ofInt_negSucc (w n : Nat) :
    BitVec.ofInt w (Int.negSucc n) = -(BitVec.ofNat w (n + 1)) := by
  have h : Int.negSucc n = -((n + 1 : Nat) : Int) := rfl
  rw [h, BitVec.ofInt_neg, BitVec.ofInt_natCast]

/-- General semantic bridge: `BitVec.ofBool b1 = BitVec.ofBool b2 ↔ b1 = b2`. -/
@[simp_llvm]
theorem bitvec_ofBool_eq_iff (b1 b2 : Bool) :
    BitVec.ofBool b1 = BitVec.ofBool b2 ↔ b1 = b2 := by
  cases b1 <;> cases b2 <;> decide

/-- General semantic bridge: `BitVec.ofBool b = 0#1 ↔ b = false`. -/
@[simp_llvm]
theorem bitvec_ofBool_eq_zero (b : Bool) :
    BitVec.ofBool b = 0#1 ↔ b = false := by
  cases b <;> decide

/-- General semantic bridge: `BitVec.ofBool b = 1#1 ↔ b = true`. -/
@[simp_llvm]
theorem bitvec_ofBool_eq_one (b : Bool) :
    BitVec.ofBool b = 1#1 ↔ b = true := by
  cases b <;> decide

/-- Lift `if` out of `Except.ok` so `evalDivRemUB` with `exact` steps deterministically. -/
@[simp_llvm, simp_step]
theorem ite_except_ok {ε α : Type} {c : Prop} [Decidable c] {x y : α} :
    (if c then (Except.ok x : Except ε α) else Except.ok y) = Except.ok (if c then x else y) := by
  by_cases hc : c <;> simp [hc]

/-- Lift `if c then .poison else x` out of `evalDivRemUB` LHS so `udiv`/`sdiv` after a
    flag-guarded op (`mul nuw`, `add nsw`, etc.) steps deterministically. -/
@[simp_llvm high, simp_step high]
theorem evalDivRemUB_ite_poison {w : Nat} {c : Prop} [Decidable c] {isS isR ex : Bool}
    {x y : IntW w} :
    evalDivRemUB isS isR ex (if c then .poison else x) y =
      if c then evalDivRemUB isS isR ex .poison y else evalDivRemUB isS isR ex x y := by
  by_cases hc : c <;> simp [hc]

@[simp_llvm]
theorem ieeeFloat_neg_neg {fmt : FloatFormat} (x : IEEEFloat fmt) : x.neg.neg = x := by
  cases x
  simp only [IEEEFloat.neg, IEEEFloat.mk.injEq]
  ext i hi
  simp; grind

/-! ### 3. Composable Refinement Tactics (`llvm_intro`, `llvm_symexec`, `llvm_vc`, `llvm_refine`) -/

section Tactics

open Lean Meta Elab Tactic

/-- Extract head definition names of `x` and `y` in `Definition.IsRefinedBy*` (when they are
    user-defined constants rather than raw `AST.Definition.mk` constructors). -/
private def getRefinementDefConsts : TacticM (List Name) := do
  let goal ← instantiateMVars (← getMainTarget)
  let fn := goal.getAppFn
  let args := goal.getAppArgs
  let pair? : Option (Expr × Expr) :=
    if fn.isConstOf ``HRefinement.IsRefinedBy && args.size ≥ 5 then
      some (args[3]!, args[4]!)
    else if fn.isConstOf ``Definition.IsRefinedBy && args.size ≥ 2 then
      some (args[0]!, args[1]!)
    else if fn.isConstOf ``Definition.IsRefinedByWith && args.size ≥ 4 then
      some (args[2]!, args[3]!)
    else if fn.isConstOf ``Definition.IsRefinedByIn && args.size ≥ 3 then
      some (args[1]!, args[2]!)
    else none
  let mut names : List Name := []
  if let some (x, y) := pair? then
    for e in [x, y] do
      let h := e.getAppFn
      if let .const nm _ := h then
        if nm != ``AST.Definition.mk && !names.contains nm then
          names := nm :: names
  return names

/-- Fuel-bounded destructuring of `hargs` after rewriting with `wellFormedForList_*_iff`. -/
private def destructArgHyps (fuel idx : Nat) (hargsId : Ident) : TacticM Unit := do
  match fuel with
  | 0 => return ()
  | fuel + 1 =>
    let argId := mkIdent (Name.mkSimple s!"arg{idx}")
    let progressed ←
      try
        evalTactic (← `(tactic|
          rcases $hargsId:ident with ⟨_, _, h_eq_args, ⟨$argId:ident, h_eq_val⟩, $hargsId:ident⟩;
          subst h_eq_val; subst h_eq_args))
        pure true
      catch _ =>
        try
          evalTactic (← `(tactic| subst $hargsId:ident))
          pure false
        catch _ =>
          pure false
    if progressed then
      destructArgHyps fuel (idx + 1) hargsId

/-- `llvm_intro` unpacks `Definition.IsRefinedBy*`, discharges `SignatureCompatible` via `rfl`,
    introduces `initMem` & `args`, destructures `args` for any arity `0..N`, and reduces
    `initCallConfig` on both source and target to `.running` configurations. -/
elab "llvm_intro" : tactic => do
  let defNames ← getRefinementDefConsts
  evalTactic (← `(tactic|
    dsimp only [HRefinement.IsRefinedBy, Refinement.IsRefinedBy, instHRefinementOfRefinement,
      Definition.IsRefinedBy, Definition.IsRefinedByWith, Definition.IsRefinedByIn]))
  evalTactic (← `(tactic| refine ⟨rfl, ?_⟩))
  let initMemId := mkIdent `initMem
  let argsId := mkIdent `args
  let hwfMemId := mkIdent `hwfMem
  let hargsId := mkIdent `hargs
  evalTactic (← `(tactic| intro $initMemId:ident $argsId:ident $hwfMemId:ident $hargsId:ident))
  for nm in defNames do
    let id := mkIdent nm
    try evalTactic (← `(tactic| dsimp only [$id:ident] at $hargsId:ident ⊢)) catch _ => pure ()
  evalTactic (← `(tactic|
    simp only [Semantics.Definition.ArgValuesWellFormed,
      RegisterValue.wellFormedForList_cons_iff, RegisterValue.wellFormedForList_nil_iff,
      RegisterValue.wellFormedFor_int_iff, RegisterValue.wellFormedFor_float_iff,
      RegisterValue.wellFormedFor_ptr_iff] at $hargsId:ident))
  destructArgHyps 32 0 hargsId
  evalTactic (← `(tactic|
    simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
      applyByValCopies, applyByValCopies.go, splitPhis,
      RegisterValue.matchesType, byvalDeferredAttrs, applyValueAttrsPure,
      List.length_nil, List.length_cons, List.any_nil, List.any_cons,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none,
      Bool.or_self, Bool.or_false, Bool.false_or, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, ite_self, List.isEmpty_nil,
      Bool.not_true, Bool.not_false, beq_self_eq_true]))

/-- Classification of the next action for a `Config` expression (O(1) AST head inspection). -/
private inductive NextAction
  | ub
  | halted
  | instr (headConst : Name)
  | term (headConst : Name)
  | unknown

/-- Inspect a `Config` expression without triggering expensive `simp` calls. -/
private def inspectConfig (c : Expr) : MetaM NextAction := do
  withTransparency .reducible do
    let c ← whnf c
    if c.isAppOf ``Config.ub then return .ub
    if c.isAppOf ``Config.halted then return .halted
    if !c.isAppOf ``Config.running then return .unknown
    let st ← whnf c.appArg!
    if !st.isAppOf ``MachineState.mk then return .unknown
    let stArgs := st.getAppArgs
    if stArgs.size < 1 then return .unknown
    let frames ← whnf stArgs[0]!
    if !frames.isAppOf ``List.cons then return .unknown
    let frame ← whnf frames.getAppArgs[1]!
    if !frame.isAppOf ``CallFrame.mk then return .unknown
    let fArgs := frame.getAppArgs
    if fArgs.size < 4 then return .unknown
    let remCode ← whnf fArgs[2]!
    let termPair ← whnf fArgs[3]!
    if remCode.isAppOf ``List.cons then
      let hd ← whnf remCode.getAppArgs[1]!
      if hd.isAppOf ``Prod.mk && hd.getAppArgs.size ≥ 4 then
        let instr ← whnf hd.getAppArgs[3]!
        if let .const nm _ := instr.getAppFn then
          return .instr nm
      return .unknown
    else if remCode.isAppOf ``List.nil then
      if termPair.isAppOf ``Prod.mk && termPair.getAppArgs.size ≥ 4 then
        let term ← whnf termPair.getAppArgs[3]!
        if let .const nm _ := term.getAppFn then
          return .term nm
      return .unknown
    else
      return .unknown

/-- Close a goal of the form `∀ res, EvalPhis ... phis res ↔ res = .ok (?ups, mem)`. -/
private def solveEvalPhis (fuel : Nat) : TacticM Unit := do
  match fuel with
  | 0 => throwError "solveEvalPhis: fuel exhausted"
  | fuel + 1 =>
    let s ← saveState
    try
      evalTactic (← `(tactic| exact fun _ => EvalPhis.nil_iff))
    catch _ =>
      restoreState s
      evalTactic (← `(tactic| intro res_phi; apply EvalPhis.cons_leaf_iff))
      evalTactic (← `(tactic| (simp [List.find?, -Prod.mk.injEq, -Option.some.injEq]; rfl)))
      evalTactic (← `(tactic| ((try llvm_step); rfl)))
      solveEvalPhis fuel

/-- Simplify a `Config.IsRefinedBy` goal immediately after taking a symbolic step. -/
private def simpAfterStep : TacticM Unit := do
  try
    evalTactic (← `(tactic|
      (try simp only [liftBinaryPure_bv, evalIntBinaryScalarPure, evalDivRemUB_ite_poison]);
      simp only [finishRegInstr, finishVoidInstr, CallFrame.advance, CallFrame.jumpTo,
        MachineState.withFrames, MachineState.withFramesAndMemory,
        commitPhiUpdates, freeAllocaList,
        applyRetFMFAndAttrsPure, applyValueAttrsPure,
        liftBinaryPure_bv, evalIntBinaryScalarPure, evalICmpScalarPure_bv,
        evalSelectPure_bv, evalSelectPure_float, evalSelectPure_ptr,
        evalConversionExec_trunc, evalConversionExec_zext, evalConversionExec_sext,
        evalFloatUnaryExec_fneg_no_nsz, evalDivRemUB_ite_poison, evalDivRemUB, ite_except_ok, RegisterValue.poisonOf,
        bitvec_ofInt_ofNat, bitvec_ofInt_neg, bitvec_ofInt_negSucc,
        BitVec.ofNat_eq_ofNat,
        AST.LlvmType.scalarType, AST.FastMathFlags.any,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
        beq_self_eq_true, Config.ofError]))
  catch _ => pure ()

/-- Step the source (`cX`) side based on its O(1)-inspected `NextAction`. -/
private def stepSourceAction (act : NextAction) : TacticM Bool := do
  match act with
  | .ub =>
    try evalTactic (← `(tactic| exact Config.IsRefinedBy.of_ub_left)); return true
    catch _ => return false
  | .instr nm =>
    if nm == ``AST.Instruction.intBinaryOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.intBinaryOp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.icmp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.icmp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.select then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.select_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.conversionOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.conversionOp_leaf_iff rfl rfl (by llvm_step; rfl) (fun _ => rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.floatUnaryOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.floatUnaryOp_leaf_iff rfl rfl (by llvm_step; rfl)
              (fun o => evalFloatUnaryExec_fneg_no_nsz _ rfl _ (by decide) _ o) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.freeze then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| apply Step.freeze_bv_val rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else return false
  | .term nm =>
    if nm == ``AST.Terminator.unreachable then
      let s ← saveState
      try evalTactic (← `(tactic| exact Config.IsRefinedBy.of_unreachable_left rfl rfl rfl)); return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.ret then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.ret_top_leaf_iff rfl rfl rfl rfl (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.retVoid then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.retVoid_top_iff rfl rfl rfl rfl none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.br then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| apply Step.br_det rfl rfl rfl))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.condBr then
      let s ← saveState
      let isPoison ←
        try
          evalTactic (← `(tactic|
            apply Config.IsRefinedBy.of_canAbort;
            apply Step.condBr_poison_canAbort rfl rfl rfl;
            (try llvm_step); (try rfl); done))
          pure true
        catch _ =>
          restoreState s
          pure false
      if isPoison then return true
      let s2 ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| apply Step.condBr_val_det rfl rfl rfl))
        evalTactic (← `(tactic| (llvm_step; rfl)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ =>
        restoreState s2
        return false
    else if nm == ``AST.Terminator.switch then
      let s ← saveState
      let isPoison ←
        try
          evalTactic (← `(tactic|
            apply Config.IsRefinedBy.of_canAbort;
            apply Step.switch_poison_canAbort rfl rfl rfl;
            (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done))
          pure true
        catch _ =>
          restoreState s
          pure false
      if isPoison then return true
      let s2 ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| apply Step.switch_val_det rfl rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?, List.find?, bitvec_ofInt_ofNat, bitvec_ofInt_negSucc]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ =>
        restoreState s2
        return false
    else return false
  | _ => return false

/-- Step the target (`cY`) side based on its O(1)-inspected `NextAction`. -/
private def stepTargetAction (act : NextAction) : TacticM Bool := do
  match act with
  | .instr nm =>
    if nm == ``AST.Instruction.intBinaryOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.intBinaryOp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.icmp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.icmp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.select then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.select_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.conversionOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.conversionOp_leaf_iff rfl rfl (by llvm_step; rfl) (fun _ => rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.floatUnaryOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.floatUnaryOp_leaf_iff rfl rfl (by llvm_step; rfl)
              (fun o => evalFloatUnaryExec_fneg_no_nsz _ rfl _ (by decide) _ o)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.freeze then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalTactic (← `(tactic| apply Step.freeze_bv_val_iff rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else return false
  | .term nm =>
    if nm == ``AST.Terminator.ret then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.ret_top_leaf_iff rfl rfl rfl rfl (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.retVoid then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.retVoid_top_iff rfl rfl rfl rfl) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.br then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalTactic (← `(tactic| apply Step.br_det_iff rfl rfl rfl))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.condBr then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalTactic (← `(tactic| apply Step.condBr_val_det_iff rfl rfl rfl))
        evalTactic (← `(tactic| ((try llvm_step); rfl)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.switch then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalTactic (← `(tactic| apply Step.switch_val_det_iff rfl rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?, List.find?, bitvec_ofInt_ofNat, bitvec_ofInt_negSucc]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else return false
  | _ => return false

/-- Try to finish a halted-vs-halted goal. -/
private def tryFinishHalted : TacticM Bool := do
  let s ← saveState
  try
    evalTactic (← `(tactic| apply Config.IsRefinedBy.of_halted_same_mem))
    return true
  catch _ =>
    restoreState s
    let s2 ← saveState
    try
      evalTactic (← `(tactic| apply Config.IsRefinedBy.of_halted))
      return true
    catch _ =>
      restoreState s2
      return false

/-- Try splitting a single `PoisonOr` hypothesis (used when symbolic `condBr`, `freeze`, or
    `evalDivRemUB` needs to inspect whether a symbolic operand is `.poison` or `.value`). -/
private def trySplitOnePoisonOr : TacticM Bool := do
  let target? ← withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← instantiateMVars decl.type
        if ty.isAppOf ``PoisonOr || ty.isAppOf ``IntW || ty.isAppOf ``FloatW then
          return some decl.userName
    return none
  if let some nm := target? then
    let id := mkIdent nm
    evalTactic (← `(tactic| cases $id:ident using PoisonOr.casesOn'))
    let gs ← getGoals
    let mut out : List MVarId := []
    for g in gs do
      setGoals [g]
      try evalTactic (← `(tactic| llvm_simp)) catch _ => pure ()
      simpAfterStep
      out := out ++ (← getGoals)
    setGoals out
    return true
  return false

private theorem bitvec1_eq_zero_or_one (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
  rcases b with ⟨⟨v, hv⟩⟩
  match v, hv with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

/-- Try splitting a symbolic `BitVec 1` hypothesis (`0#1` vs `1#1`) for `condBr`. -/
private def trySplitOneBoolBv : TacticM Bool := do
  let target? ← withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← instantiateMVars decl.type
        if ty.isAppOf ``BitVec && ty.getAppArgs.size == 1 then
          if ty.getAppArgs[0]! == mkNatLit 1 then
            return some decl.userName
    return none
  if let some nm := target? then
    let id := mkIdent nm
    let s ← saveState
    try
      evalTactic (← `(tactic|
        rcases bitvec1_eq_zero_or_one $id:ident with h_bv1_eq | h_bv1_eq <;> subst h_bv1_eq))
      let gs ← getGoals
      let mut out : List MVarId := []
      for g in gs do
        setGoals [g]
        try evalTactic (← `(tactic| llvm_simp)) catch _ => pure ()
        simpAfterStep
        out := out ++ (← getGoals)
      setGoals out
      return true
    catch _ =>
      restoreState s
      return false
  return false

/-- Handle nondeterministic `freeze` on `.poison` (peeling target via `of_freeze_poison_right` first,
    then matching source via `freeze_bv_poison_step`). -/
private def tryStepFreezePoison (actX actY : NextAction) : TacticM Bool := do
  -- 1. If target is `freeze` on `.poison`, peel target universally first
  if let .instr nmY := actY then
    if nmY == ``AST.Instruction.freeze then
      let s ← saveState
      try
        let bId := mkIdent `b_frz
        let hmId := mkIdent `hmode_frz
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_freeze_poison_right rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        evalTactic (← `(tactic| intro $bId:ident $hmId:ident))
        simpAfterStep
        return true
      catch _ =>
        restoreState s
  -- 2. If source is `freeze` on `.poison`, step source using `b_frz` / `hmode_frz` if present, else `0`
  if let .instr nmX := actX then
    if nmX == ``AST.Instruction.freeze then
      let s1 ← saveState
      try
        let bId := mkIdent `b_frz
        let hmId := mkIdent `hmode_frz
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| refine Step.freeze_bv_poison_step rfl rfl ?_ $bId:ident $hmId:ident))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        simpAfterStep
        return true
      catch _ =>
        restoreState s1
        let s2 ← saveState
        try
          evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
          evalTactic (← `(tactic| apply Step.freeze_bv_poison_zero rfl rfl))
          focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
          simpAfterStep
          return true
        catch _ =>
          restoreState s2
  return false

/-- Fuel-bounded symbolic execution loop on all open `Config.IsRefinedBy` goals. -/
private def symexecLoop (fuel : Nat) : TacticM Unit := do
  match fuel with
  | 0 => return ()
  | fuel + 1 =>
    let goals ← getGoals
    if goals.isEmpty then return ()
    let mut anyProgress := false
    let mut remaining : List MVarId := []
    for g in goals do
      setGoals [g]
      let tgt ← instantiateMVars (← getMainTarget)
      if tgt.isAppOf ``Config.IsRefinedBy && tgt.getAppArgs.size ≥ 3 then
        let cX := tgt.getAppArgs[1]!
        let cY := tgt.getAppArgs[2]!
        let (actX, actY) ← withMainContext do
          return (← inspectConfig cX, ← inspectConfig cY)
        match actX, actY with
        | .halted, .halted =>
          if ← tryFinishHalted then
            anyProgress := true
            remaining := remaining ++ (← getGoals)
          else
            remaining := remaining ++ [g]
        | _, _ =>
          let p1 ← stepSourceAction actX
          if p1 then
            anyProgress := true
            remaining := remaining ++ (← getGoals)
          else
            let p2 ← stepTargetAction actY
            if p2 then
              anyProgress := true
              remaining := remaining ++ (← getGoals)
            else
              -- Try nondeterministic `freeze` on `.poison`
              let p3 ← tryStepFreezePoison actX actY
              if p3 then
                anyProgress := true
                remaining := remaining ++ (← getGoals)
              else
                -- Try simplifying / splitting when stuck on symbolic `condBr`, `switch`, `freeze`, or `div`/`rem`
                let needsSplit :=
                  match actX, actY with
                  | .term ``AST.Terminator.condBr, _ => true
                  | _, .term ``AST.Terminator.condBr => true
                  | .term ``AST.Terminator.switch, _ => true
                  | _, .term ``AST.Terminator.switch => true
                  | .instr ``AST.Instruction.freeze, _ => true
                  | _, .instr ``AST.Instruction.freeze => true
                  | .unknown, _ => true
                  | _, .unknown => true
                  | _, _ => false
                if needsSplit then
                  let p4 ← trySplitOnePoisonOr
                  if p4 then
                    anyProgress := true
                    remaining := remaining ++ (← getGoals)
                  else
                    let p5 ← trySplitOneBoolBv
                    if p5 then
                      anyProgress := true
                      remaining := remaining ++ (← getGoals)
                    else
                      let sSplit ← saveState
                      let p6 ←
                        try
                          let cond? ← withMainContext do
                            let tgt ← instantiateMVars (← getMainTarget)
                            let found := tgt.find? fun e => e.isAppOf ``ite && e.getAppArgs.size ≥ 5
                            match found with
                            | some e => return some e.getAppArgs[1]!
                            | none => return none
                          if let some condExpr := cond? then
                            let hName := mkIdent `h_ite_sym
                            let condStx ← withMainContext (Lean.PrettyPrinter.delab condExpr)
                            evalTactic (← `(tactic| by_cases $hName:ident : $condStx))
                            let gs ← getGoals
                            let mut out : List MVarId := []
                            for sg in gs do
                              setGoals [sg]
                              try evalTactic (← `(tactic| simp only [$hName:ident, ↓reduceIte, not_false_eq_true])) catch _ => pure ()
                              simpAfterStep
                              out := out ++ (← getGoals)
                            setGoals out
                            pure true
                          else
                            pure false
                        catch _ =>
                          restoreState sSplit
                          pure false
                      if p6 then
                        anyProgress := true
                        remaining := remaining ++ (← getGoals)
                      else
                        remaining := remaining ++ [g]
                else
                  remaining := remaining ++ [g]
      else
        remaining := remaining ++ [g]
    setGoals remaining
    if anyProgress then
      symexecLoop fuel

/-- `llvm_symexec` symbolically executes deterministic silent instructions and terminators on
    source and target using O(1) AST head dispatch, handles symbolic `condBr`/`switch` branching
    and nondeterministic `freeze`, closes `.ub` / `unreachable` / `condBr poison` / `switch poison`
    goals immediately, and reduces `.halted` vs `.halted` to `RegisterValue.IsRefinedBy .id retX retY`. -/
elab "llvm_symexec" : tactic => do
  symexecLoop 128

/-- Split all `PoisonOr` local hypotheses (`arg0`, `arg1`, ...) so pure evaluators reduce cleanly. -/
private def splitPoisonOrHyps (fuel : Nat) : TacticM Unit := do
  match fuel with
  | 0 => return ()
  | fuel + 1 =>
    let target? ← withMainContext do
      let lctx ← getLCtx
      for decl in lctx do
        if !decl.isImplementationDetail then
          let ty ← instantiateMVars decl.type
          if ty.isAppOf ``PoisonOr || ty.isAppOf ``IntW || ty.isAppOf ``FloatW then
            return some decl.userName
      return none
    if let some nm := target? then
      let id := mkIdent nm
      evalTactic (← `(tactic| cases $id:ident using PoisonOr.casesOn'))
      let subgoals ← getGoals
      let mut out : List MVarId := []
      for sg in subgoals do
        setGoals [sg]
        splitPoisonOrHyps fuel
        out := out ++ (← getGoals)
      setGoals out

/-- Close only trivial LLVM-level verification conditions (reflexivity, poison, contradiction). -/
private def closeTrivialVc : TacticM Unit := do
  let s ← saveState
  try
    evalTactic (← `(tactic|
      (try intros);
      first
      | (rfl; done)
      | (trivial; done)
      | (contradiction; done)
      | (exact RegisterValue.IsRefinedBy.refl _; done)
      | (exact RegisterValue.isRefinedBy_bv_poison; done)
      | (exact RegisterValue.isRefinedBy_float_poison; done)
      | (exact RegisterValue.isRefinedBy_ptr_poison; done)))
  catch _ =>
    restoreState s

/-- `llvm_vc` extracts clean, pure Lean verification conditions (`BitVec` / `Bool` / `Float`)
    from `RegisterValue.IsRefinedBy` goals by splitting `PoisonOr` hypotheses (auto-closing
    `.poison ⊒ _`), unfolding pure LLVM evaluators and poison guards with `simp_llvm`, splitting
    remaining `if`/`match` guards, and closing trivial reflexive/contradictory branches. -/
elab "llvm_vc" : tactic => do
  let allGoals ← getGoals
  if allGoals.isEmpty then return ()
  let mut finalRemaining : List MVarId := []
  for rootGoal in allGoals do
    setGoals [rootGoal]
    let tgt ← instantiateMVars (← getMainTarget)
    if tgt.isAppOf ``Config.IsRefinedBy then
      finalRemaining := finalRemaining ++ [rootGoal]
      continue
    -- Fast path: try closing without splitting `PoisonOr` (rollback if not closed)
    let sFast ← saveState
    let closedFast ←
      try
        evalTactic (← `(tactic|
          first
          | exact RegisterValue.IsRefinedBy.refl _
          | (llvm_simp; exact RegisterValue.IsRefinedBy.refl _)
          | (llvm_simp; rfl)))
        pure (← getGoals).isEmpty
      catch _ =>
        pure false
    if closedFast then continue
    restoreState sFast
    -- General path: lift to PoisonOr.IsRefinedBy, split PoisonOr hypotheses, unfold guards
    try evalTactic (← `(tactic|
      first
      | apply RegisterValue.isRefinedBy_bv_of_poisonOr
      | apply RegisterValue.isRefinedBy_float_of_poisonOr)) catch _ => pure ()
    splitPoisonOrHyps 8
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      try evalTactic (← `(tactic| llvm_simp)) catch _ => pure ()
      if !(← getGoals).isEmpty then
        closeTrivialVc
      let cur ← getGoals
      for cg in cur do
        setGoals [cg]
        try
          evalTactic (← `(tactic| (repeat split); all_goals (try split at *)))
          evalTactic (← `(tactic| all_goals (try simp only [PoisonOr.value, PoisonOr.mk.injEq, Option.some.injEq] at *)))
          evalTactic (← `(tactic| all_goals (try subst_vars)))
          evalTactic (← `(tactic| all_goals (repeat split)))
          evalTactic (← `(tactic| all_goals (try llvm_simp)))
        catch _ => pure ()
        let leaves ← getGoals
        for lg in leaves do
          setGoals [lg]
          closeTrivialVc
          finalRemaining := finalRemaining ++ (← getGoals)
  setGoals finalRemaining

/-- Transparent refinement tactic: runs `llvm_intro; llvm_symexec; llvm_vc` and tries standard
    Lean closers (`rfl`, `trivial`, `contradiction`, `grind`, `bv_omega`, `ext _ _; simp; grind`).
    Any remaining pure verification condition is left exposed for an explicit Lean proof. -/
macro "llvm_refine" : tactic =>
  `(tactic| (llvm_intro; llvm_symexec; llvm_vc;
             all_goals (try (first
               | (rfl; done)
               | (trivial; done)
               | (contradiction; done)
               | (grind; done)
               | (bv_omega; done)
               | (ext _ _; simp; (try grind); done)))))

end Tactics

end LeanNanoLlvm.Refinement
