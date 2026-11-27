import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem fneg_fneg_float :
    [llvm-definition|
      define float @f(float %x) {
      entry:
        %t = fneg float %x
        %r = fneg float %t
        ret float %r
      }
    ] ⊒ [llvm-definition|
      define float @f(float %x) {
      entry:
        ret float %x
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
