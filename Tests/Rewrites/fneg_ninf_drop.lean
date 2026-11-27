import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem fneg_ninf_drop :
    [llvm-definition|
      define double @f(double %x) {
      entry:
        %r = fneg ninf double %x
        ret double %r
      }
    ] ⊒ [llvm-definition|
      define double @f(double %x) {
      entry:
        %r = fneg double %x
        ret double %r
      }
    ] := by
  llvm_refine
  intro _; simp [handleFMF, PoisonOr.isRefinedBy_ite_poison]; intro _; rfl

end LeanNanoLlvm.Tests.Rewrites
