import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem urem_pow2_to_and_256 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = urem i32 %x, 256
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = and i32 %x, 255
        ret i32 %r
      }
    ] := by
  llvm_refine
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, BitVec.toNat_and]
  exact (Nat.and_two_pow_sub_one_eq_mod _ 8).symm

end LeanNanoLlvm.Tests.Rewrites
