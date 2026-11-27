import Lean
import LeanNanoLlvm.Refinement.Refinement

/-! # Refinement Simp Lemmas (`simp_llvm` / `simp_step`)

Well-formedness destructuring lemmas, semantic bridges and `simp_llvm` / `simp_step`
normalization lemmas used by the refinement tactics in `LeanNanoLlvm.Refinement.Tactic`
and by `llvm_disprove`. Kept separate from the tactic implementation so tactic edits
do not recompile these lemmas, and so `llvm_disprove` does not depend on `llvm_refine`. -/

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

end LeanNanoLlvm.Refinement
