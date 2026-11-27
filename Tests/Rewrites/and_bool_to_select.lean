import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

/-- Sound Alive2 direction: `and i1 %c, %b ⊒ select i1 %c, %b, false` (the converse is unsound when `%b` is poison). -/
theorem and_bool_to_select :
    [llvm-definition|
      define i1 @f(i1 %c, i1 %b) {
      entry:
        %r = and i1 %c, %b
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i1 %c, i1 %b) {
      entry:
        %r = select i1 %c, i1 %b, i1 false
        ret i1 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
