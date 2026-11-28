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


/-- T2: the witness search is bounded by heartbeats, not wall-clock time, so its outcome does not
depend on the machine's load. A budget of one thousand heartbeats is too small for this
three-argument search (it fails, deterministically); the default budget finds the witness. -/
example : True := by
  fail_if_success
    have : ¬ ([llvm-definition|
      define i32 @f(i32 %x, i32 %y, i32 %z) {
      entry:
        %a = mul i32 %x, %y
        %b = mul i32 %a, %z
        ret i32 %b
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x, i32 %y, i32 %z) {
      entry:
        %a = mul i32 %x, %z
        %b = mul i32 %a, %x
        ret i32 %b
      }
    ]) := by llvm_disprove (heartbeats := 1)
  trivial

example : ¬ ([llvm-definition|
      define i32 @f(i32 %x, i32 %y, i32 %z) {
      entry:
        %a = mul i32 %x, %y
        %b = mul i32 %a, %z
        ret i32 %b
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x, i32 %y, i32 %z) {
      entry:
        %a = mul i32 %x, %z
        %b = mul i32 %a, %x
        ret i32 %b
      }
    ]) := by llvm_disprove

/-- T3: the certifier used to step both programs with deterministic-step lemmas for a fixed set of
instructions, so a valid witness through a loop, an intrinsic call or `ret void` could not be
certified ("could not close refutation goal"). The target's behaviour is now certified by
running the executable interpreter in the kernel (`runSteps_sound`), and the source side has
lemmas for intrinsic calls, `extractvalue`, `fcmp` and `ret void`. Pair `0076a63f65e69b99`
(InstCombine, an `assume` on the exit count; `%n = 3` makes the target's `assume` false). -/
example : ¬ ([llvm-definition|
      define void @f(i32 %n) {
      entry:
        br label %loop
      loop:
        %i = phi i32 [0, %entry], [%i.next, %loop]
        %i.next = add i32 %i, 1
        %cond_i = icmp ult i32 %i, %n
        %cond_i2 = icmp ult i32 %i, 2
        %cond = select i1 %cond_i, i1 %cond_i2, i1 false
        br i1 %cond, label %loop, label %exit
      exit:
        ret void
      }
    ] ⊒ [llvm-definition|
      define void @f(i32 %n) {
      entry:
        br label %loop
      loop:
        %i = phi i32 [0, %entry], [%i.next, %loop]
        %i.next = add i32 %i, 1
        %cond_i = icmp ult i32 %i, %n
        %cond_i2 = icmp ult i32 %i, -1
        %cond = select i1 %cond_i, i1 %cond_i2, i1 false
        br i1 %cond, label %loop, label %exit
      exit:
        %n_m_min = call i32 @llvm.umin.i32(i32 %n, i32 2)
        %ExactNotTaken = icmp eq i32 %i, %n_m_min
        call void @llvm.assume(i1 %ExactNotTaken)
        ret void
      }
    ]) := by llvm_disprove [.bv 32 (.value 3#32)]

/-- T3, source side: an intrinsic call (`llvm.umax`) on the source, a different result on the
target. -/
example : ¬ ([llvm-definition|
      define i8 @f(i8 %x) {
      entry:
        %m = call i8 @llvm.umax.i8(i8 %x, i8 10)
        ret i8 %m
      }
    ] ⊒ [llvm-definition|
      define i8 @f(i8 %x) {
      entry:
        ret i8 %x
      }
    ]) := by llvm_disprove

end LeanNanoLlvm.Tests.Refinement.Difftest
