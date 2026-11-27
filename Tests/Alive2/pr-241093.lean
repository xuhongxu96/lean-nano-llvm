import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

-- LLVM PR #241093: `[InstCombine] Fold and/or of xors with a common operand and constants`
-- https://github.com/llvm/llvm-project/pull/241093
-- Alive2: https://alive2.llvm.org/ce/z/-WGc52

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open LeanNanoLlvm.Tests.Rewrites
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_241093_or (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %c1, i$(w) %c2) {
      entry:
        %a = xor i$(w) %x, %c1
        %b = xor i$(w) %x, %c2
        %r = or i$(w) %a, %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %c1, i$(w) %c2) {
      entry:
        %a = xor i$(w) %x, %c1
        %c = xor i$(w) %c1, %c2
        %r = or i$(w) %a, %c
        ret i$(w) %r
      }
    ] := by llvm_refine

theorem pr_241093_and (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %c1, i$(w) %c2) {
      entry:
        %a = xor i$(w) %x, %c1
        %b = xor i$(w) %x, %c2
        %r = and i$(w) %a, %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %c1, i$(w) %c2) {
      entry:
        %a = xor i$(w) %x, %c1
        %c = xor i$(w) %c1, %c2
        %nc = xor i$(w) %c, -1
        %r = and i$(w) %a, %nc
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  rename_i x c1 c2
  rw [neg_one_eq_allOnes]; ext i hi; simp
  cases x[i] <;> cases c1[i] <;> cases c2[i] <;> rfl

end LeanNanoLlvm.Tests.Alive2
