import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem fneg_fneg_double :
    [llvm-definition|
      define double @f(double %x) {
      entry:
        %t = fneg double %x
        %r = fneg double %t
        ret double %r
      }
    ] ⊒ [llvm-definition|
      define double @f(double %x) {
      entry:
        ret double %x
      }
    ] := by
  llvm_refine
  simp [handleFMF, PoisonOr.IsRefinedBy] at *; subst_vars; exact ieeeFloat_neg_neg _

end LeanNanoLlvm.Tests.Rewrites
