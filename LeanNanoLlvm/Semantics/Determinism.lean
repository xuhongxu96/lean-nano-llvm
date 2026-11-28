import LeanNanoLlvm.Semantics.Exec

/-! # Determinism of the relational semantics on choice-free steps

`Step` is the specification and `execStep` an executable interpreter proved sound against it
(`execStep_sound`: every interpreter step is a `Step`). This file proves the converse where the
specification itself leaves no choice: when a step's operands take no choice and its outcome does
not depend on the interpreter's oracle, every `Step` from that configuration is the
interpreter's step, up to the text of error messages (which `Step` leaves free in some rules and
which no refinement observes). A refutation (`llvm_disprove`) can then certify the source
program's behaviour, which must be known completely, by running the interpreter.

The choices `Step` allows are: `undef` operands (`UndefValRel`), conversion constants and
operations, floating-point and intrinsic results (`∃` an oracle), undefined bits read from memory
(`BytesToValueRel`), `freeze` of poison (`FreezeRel`), and the addresses of new objects
(`AllocSpec`). The oracle-quantified ones are covered by the hypothesis that the interpreter's
outcome is the same for every oracle; the others by computable side conditions. -/

namespace LeanNanoLlvm.AST

/-! ## Choice-free expressions -/

mutual
/-- An expression whose evaluation takes no choice: no `undef` (any value) and no conversion
constant (an oracle-dependent conversion) anywhere in it. -/
def Exp.choiceFree : Exp → Bool
  | .undef => false
  | .convConst .. => false
  | .array es => Exp.choiceFreeList es
  | .struct _ es => Exp.choiceFreeList es
  | .vector es => Exp.choiceFreeList es
  | .splat (_, e) => Exp.choiceFree e
  | .gepConst _ _ (_, p) idxs => Exp.choiceFree p && Exp.choiceFreeList idxs
  | .binConst _ _ a b => Exp.choiceFree a && Exp.choiceFree b
  | .extractElemConst _ a _ b => Exp.choiceFree a && Exp.choiceFree b
  | .shuffleVecConst _ a b _ => Exp.choiceFree a && Exp.choiceFree b
  | .insertElemConst _ a _ b _ c => Exp.choiceFree a && Exp.choiceFree b && Exp.choiceFree c
  | _ => true

/-- `Exp.choiceFree` for every element. -/
def Exp.choiceFreeList : List (LlvmType × Exp) → Bool
  | [] => true
  | (_, e) :: rest => Exp.choiceFree e && Exp.choiceFreeList rest
end

end LeanNanoLlvm.AST

namespace LeanNanoLlvm.Semantics

open AST

/-! ## Results up to error messages -/

/-- An error with its message erased. -/
def _root_.LeanNanoLlvm.ExecError.erase : ExecError → ExecError
  | .immediateUB _ => .immediateUB ""
  | .staticError _ => .staticError ""
  | e => e

/-- A relational result `r` and the interpreter's result `x` agree: the same value and memory with
the oracle state `o` untouched, or errors of the same kind. -/
def ResAgrees {α : Type} (o : OracleState) :
    Except ExecError (α × MemoryState) → Except ExecError (α × MemoryState × OracleState) → Prop
  | .ok (v, m), x => x = .ok (v, m, o)
  | .error e, x => ∃ e', x = .error e' ∧ e'.erase = e.erase

/-- Errors of the same kind agree, whatever their messages. -/
theorem ResAgrees.of_error {α : Type} {o : OracleState} {e : ExecError}
    {x : Except ExecError (α × MemoryState × OracleState)} (e' : ExecError)
    (hx : x = .error e') (he : e'.erase = e.erase) : ResAgrees o (.error e) x := ⟨e', hx, he⟩

/-- A static error agrees with any static error. -/
theorem ResAgrees.of_static {α : Type} {o : OracleState} {m : String}
    {x : Except ExecError (α × MemoryState × OracleState)}
    (h : ∃ m', x = .error (.staticError m')) : ResAgrees o (.error (.staticError m)) x := by
  obtain ⟨m', hx⟩ := h; exact ⟨_, hx, rfl⟩

/-! ## Expressions -/

/-- A pure leaf evaluates, in the interpreter, to its value without touching memory or the oracle. -/
theorem execExp_of_leaf {dl cfg regs mem ty e r} (o : OracleState)
    (h : evalPureLeafExp? dl cfg regs mem ty e = some r) :
    execExp dl cfg regs mem ty e o = r.map (fun v => (v, mem, o)) := by
  have key : ∀ (x : Except ExecError RegisterValue), some x = some r → r = x := fun x hx => (Option.some.inj hx).symm
  cases e with
  | identifier id =>
    cases id with
    | local_id i =>
      rw [key _ h]; unfold execExp; cases regs.get? (.local_id i) <;> rfl
    | global_id i =>
      rw [key _ h]; unfold execExp
      cases mem.globalAddrs.get? i <;> (try cases mem.funcAddrs.get? i) <;> rfl
  | bool b =>
    rw [key _ h]; unfold execExp
    cases ty with
    | int w => rcases w with _ | _ | w <;> rfl
    | _ => rfl
  | int x => rw [key _ h]; unfold execExp; cases ty <;> rfl
  | floatBits b => rw [key _ h]; unfold execExp; cases ty <;> rfl
  | floatDec n m e => rw [key _ h]; unfold execExp; cases ty <;> rfl
  | floatSpecial a b c d => rw [key _ h]; unfold execExp; cases ty <;> rfl
  | blockAddress f b =>
    rw [key _ h]; unfold execExp
    cases ty with
    | ptr a => simp only [blockAddrKey]; split <;> rename_i heq <;> simp [heq, Except.map]
    | _ => rfl
  | null => rw [key _ h]; unfold execExp; cases ty <;> rfl
  | zeroinitializer => rw [key _ h]; rfl
  | poison => rw [key _ h]; rfl
  | _ => simp [evalPureLeafExp?] at h

set_option maxHeartbeats 1600000 in
mutual
/-- Relational evaluation of a choice-free expression is the interpreter's (for every oracle). -/
theorem EvalExp.exec_agrees {dl cfg regs mem ty e r}
    (h : EvalExp dl cfg regs mem ty e r) (hcf : e.choiceFree = true) (o : OracleState) :
    ResAgrees o r (execExp dl cfg regs mem ty e o) := by
  cases h with
  | leaf_ok hl => simp only [ResAgrees, execExp_of_leaf o hl, Except.map]
  | leaf_err hl => exact ⟨_, by rw [execExp_of_leaf o hl]; rfl, rfl⟩
  | undef_ok _ _ => simp [Exp.choiceFree] at hcf
  | undef_err _ => simp [Exp.choiceFree] at hcf
  | convConst_ok _ _ => simp [Exp.choiceFree] at hcf
  | convConst_arg_err _ => simp [Exp.choiceFree] at hcf
  | convConst_eval_err _ _ => simp [Exp.choiceFree] at hcf
  | array_ok hlen hl =>
    have a := EvalExpList.exec_agrees hl (by simpa [Exp.choiceFree] using hcf) o
    simp only [ResAgrees] at a ⊢; unfold execExp; simp [hlen, a]
  | array_err hlen hl =>
    obtain ⟨e', hx, he⟩ := EvalExpList.exec_agrees hl (by simpa [Exp.choiceFree] using hcf) o
    exact ⟨e', by unfold execExp; simp [hlen, hx], he⟩
  | array_len_err hlen =>
    apply ResAgrees.of_static
    unfold execExp; simp [hlen]
  | array_ty_err hty =>
    apply ResAgrees.of_static
    unfold execExp; cases ty <;> simp_all [LlvmType.asArray?]
  | struct_ok hlen hl =>
    have a := EvalExpList.exec_agrees hl (by simpa [Exp.choiceFree] using hcf) o
    simp only [ResAgrees] at a ⊢; unfold execExp; simp [hlen, a]
  | struct_err hlen hl =>
    obtain ⟨e', hx, he⟩ := EvalExpList.exec_agrees hl (by simpa [Exp.choiceFree] using hcf) o
    exact ⟨e', by unfold execExp; simp [hlen, hx], he⟩
  | struct_len_err hlen =>
    apply ResAgrees.of_static
    unfold execExp; simp [hlen]
  | struct_ty_err hty =>
    apply ResAgrees.of_static
    unfold execExp; cases ty <;> simp_all [LlvmType.asStruct?]
  | vector_ok hlen hl =>
    have a := EvalExpList.exec_agrees hl (by simpa [Exp.choiceFree] using hcf) o
    simp only [ResAgrees] at a ⊢; unfold execExp; simp [hlen, a]
  | vector_err hlen hl =>
    obtain ⟨e', hx, he⟩ := EvalExpList.exec_agrees hl (by simpa [Exp.choiceFree] using hcf) o
    exact ⟨e', by unfold execExp; simp [hlen, hx], he⟩
  | vector_len_err hlen =>
    apply ResAgrees.of_static
    unfold execExp; simp [hlen]
  | vector_ty_err hty =>
    apply ResAgrees.of_static
    unfold execExp; cases ty <;> simp_all [LlvmType.asVector?]
  | splat_ok he =>
    have a := EvalExp.exec_agrees he (by simpa [Exp.choiceFree] using hcf) o
    simp only [ResAgrees] at a ⊢; unfold execExp; simp [a]
  | splat_err he =>
    obtain ⟨e', hx, he'⟩ := EvalExp.exec_agrees he (by simpa [Exp.choiceFree] using hcf) o
    exact ⟨e', by unfold execExp; simp [hx], he'⟩
  | splat_ty_err hty =>
    apply ResAgrees.of_static
    unfold execExp; cases ty <;> simp_all [LlvmType.asVector?]
  | gepConst_ok hb hi hg =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees hb hcf.1 o
    have a2 := EvalExpList.exec_agrees hi hcf.2 o
    simp only [ResAgrees] at a1 a2 ⊢; unfold execExp; simp [a1, a2, hg]
  | gepConst_base_err hb =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees hb hcf.1 o
    exact ⟨e', by unfold execExp; simp [hx], he⟩
  | gepConst_idx_err hb hi =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees hb hcf.1 o
    have a2 := EvalExpList.exec_agrees hi hcf.2 o
    simp only [ResAgrees] at a1 a2
    obtain ⟨e', hx, he⟩ := a2
    exact ⟨e', by unfold execExp; simp [a1, hx], he⟩
  | gepConst_eval_err hb hi hg =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees hb hcf.1 o
    have a2 := EvalExpList.exec_agrees hi hcf.2 o
    simp only [ResAgrees] at a1 a2
    apply ResAgrees.of_error
    · unfold execExp; simp [a1, a2, hg]; try rfl
    · rfl
  | binConst_ok h1 h2 hb =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    have a2 := EvalExp.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1 a2 ⊢; unfold execExp; simp [a1, a2, hb]
  | binConst_lhs_err h1 =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h1 hcf.1 o
    exact ⟨e', by unfold execExp; simp [hx], he⟩
  | binConst_rhs_err h1 h2 =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1
    exact ⟨e', by unfold execExp; simp [a1, hx], he⟩
  | binConst_eval_err h1 h2 hb =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    have a2 := EvalExp.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1 a2
    apply ResAgrees.of_error
    · unfold execExp; simp [a1, a2, hb]; try rfl
    · rfl
  | insertElemConst_ok h1 h2 h3 hb =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1.1 o
    have a2 := EvalExp.exec_agrees h2 hcf.1.2 o
    have a3 := EvalExp.exec_agrees h3 hcf.2 o
    simp only [ResAgrees] at a1 a2 a3 ⊢; unfold execExp; simp [a1, a2, a3, hb]
  | insertElemConst_vec_err h1 =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h1 hcf.1.1 o
    exact ⟨e', by unfold execExp; simp [hx], he⟩
  | insertElemConst_elem_err h1 h2 =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1.1 o
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h2 hcf.1.2 o
    simp only [ResAgrees] at a1
    exact ⟨e', by unfold execExp; simp [a1, hx], he⟩
  | insertElemConst_idx_err h1 h2 h3 =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1.1 o
    have a2 := EvalExp.exec_agrees h2 hcf.1.2 o
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h3 hcf.2 o
    simp only [ResAgrees] at a1 a2
    exact ⟨e', by unfold execExp; simp [a1, a2, hx], he⟩
  | insertElemConst_eval_err h1 h2 h3 hb =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1.1 o
    have a2 := EvalExp.exec_agrees h2 hcf.1.2 o
    have a3 := EvalExp.exec_agrees h3 hcf.2 o
    simp only [ResAgrees] at a1 a2 a3
    apply ResAgrees.of_error
    · unfold execExp; simp [a1, a2, a3, hb]; try rfl
    · rfl
  | extractElemConst_ok h1 h2 hb =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    have a2 := EvalExp.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1 a2 ⊢; unfold execExp; simp [a1, a2, hb]
  | extractElemConst_vec_err h1 =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h1 hcf.1 o
    exact ⟨e', by unfold execExp; simp [hx], he⟩
  | extractElemConst_idx_err h1 h2 =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1
    exact ⟨e', by unfold execExp; simp [a1, hx], he⟩
  | extractElemConst_eval_err h1 h2 hb =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    have a2 := EvalExp.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1 a2
    apply ResAgrees.of_error
    · unfold execExp; simp [a1, a2, hb]; try rfl
    · rfl
  | shuffleVecConst_ok h1 h2 hb =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    have a2 := EvalExp.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1 a2 ⊢; unfold execExp; simp [a1, a2, hb]
  | shuffleVecConst_e1_err h1 =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h1 hcf.1 o
    exact ⟨e', by unfold execExp; simp [hx], he⟩
  | shuffleVecConst_e2_err h1 h2 =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1
    exact ⟨e', by unfold execExp; simp [a1, hx], he⟩
  | shuffleVecConst_eval_err h1 h2 hb =>
    simp only [Exp.choiceFree, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    have a2 := EvalExp.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1 a2
    apply ResAgrees.of_error
    · unfold execExp; simp [a1, a2, hb]; try rfl
    · rfl

/-- `EvalExp.exec_agrees` for expression lists. -/
theorem EvalExpList.exec_agrees {dl cfg regs mem es r}
    (h : EvalExpList dl cfg regs mem es r) (hcf : Exp.choiceFreeList es = true) (o : OracleState) :
    ResAgrees o r (execExpList dl cfg regs mem es o) := by
  cases h with
  | nil => rfl
  | cons_ok h1 h2 =>
    simp only [Exp.choiceFreeList, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    have a2 := EvalExpList.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1 a2 ⊢
    simp [execExpList, a1, a2]
  | cons_head_err h1 =>
    simp only [Exp.choiceFreeList, Bool.and_eq_true] at hcf
    obtain ⟨e', hx, he⟩ := EvalExp.exec_agrees h1 hcf.1 o
    exact ⟨e', by simp [execExpList, hx], he⟩
  | cons_tail_err h1 h2 =>
    simp only [Exp.choiceFreeList, Bool.and_eq_true] at hcf
    have a1 := EvalExp.exec_agrees h1 hcf.1 o
    obtain ⟨e', hx, he⟩ := EvalExpList.exec_agrees h2 hcf.2 o
    simp only [ResAgrees] at a1
    exact ⟨e', by simp [execExpList, a1, hx], he⟩
end


end LeanNanoLlvm.Semantics
