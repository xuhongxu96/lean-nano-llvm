import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem fneg_nnan_drop :
    [llvm-definition|
      define float @f(float %x) {
      entry:
        %r = fneg nnan float %x
        ret float %r
      }
    ] ⊒ [llvm-definition|
      define float @f(float %x) {
      entry:
        %r = fneg float %x
        ret float %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
