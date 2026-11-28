import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.Refinement.Disprove
import LeanNanoLlvm.AST.Syntax

/-!
# Regressions from the differential campaign (`difftest/BUGS.md`)

Lean-level counterparts of the `Tests/ll` reproducers, for bugs that affect the refinement
relation and the proof tactics rather than (only) the interpreter.
-/

namespace LeanNanoLlvm.Tests.Refinement.Difftest

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

/-- B1: poison-generating attributes apply before `noundef`, whatever their order. A value made
poison by `range` on a `noundef` parameter is immediate UB (it used to pass `noundef` first). -/
example : (match applyValueAttrsPure .default64LE {} (.int 8) (.bv 8 (.value 5#8))
    [.noundef, .range 0 2] with
    | .error (.immediateUB _) => true
    | _ => false) = true := by decide

/-- B1 at the refinement level: Alive2 test pair `ef0c2671893037dc` (`select` on a `trunc nuw`
that is always poison for in-range inputs) is a correct transformation; the witness `%x = 0`
violates `range` on a `noundef` parameter, which is UB, so it must not refute it. -/
example : True := by
  fail_if_success
    have : ¬ ([llvm-definition|
      define i1 @f(i1 %c, i8 noundef range(-32, -16) %x) {
      entry:
        %t = trunc nuw nsw i8 %x to i4
        %s = select i1 %c, i4 3, i4 %t
        %r = trunc i4 %s to i1
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i1 %c, i8 noundef range(-32, -16) %x) {
      entry:
        %t = trunc i8 %x to i1
        %r = or i1 %c, %t
        ret i1 %r
      }
    ]) := by llvm_disprove
  trivial

/-- T1: the witness search runs candidates with constant stack. A data-dependent loop with a large
trip count used to abort Lean ("deep recursion was detected at 'interpreter'"); now the search
simply finds no counterexample (the pair is correct). -/
example : True := by
  fail_if_success
    have : ¬ ([llvm-definition|
      define i32 @f(i32 %n) {
      entry:
        br label %body
      body:
        %i = phi i32 [0, %entry], [%i.next, %body]
        %a = phi i32 [0, %entry], [%a.next, %body]
        %a.next = add i32 %a, 2
        %i.next = add i32 %i, 1
        %cmp = icmp eq i32 %i.next, %n
        br i1 %cmp, label %exit, label %body
      exit:
        ret i32 %a.next
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %n) {
      entry:
        br label %body
      body:
        %i = phi i32 [0, %entry], [%i.next, %body]
        %a = phi i32 [0, %entry], [%a.next, %body]
        %a.next = add i32 %a, 2
        %i.next = add i32 %i, 1
        %cmp = icmp eq i32 %i.next, %n
        br i1 %cmp, label %exit, label %body
      exit:
        ret i32 %a.next
      }
    ]) := by llvm_disprove
  trivial

end LeanNanoLlvm.Tests.Refinement.Difftest
