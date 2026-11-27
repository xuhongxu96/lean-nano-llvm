import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics
import Tests.Semantics.Helpers

/-! Semantics tests: control flow, `phi`, `switch`, recursion, indirect calls, aggregates, vectors. -/

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Control Flow, Parallel `phi`, `switch`, Recursion, Indirect Calls, Aggregates & Vectors -/

/-- Parallel `phi` test via Fibonacci loop (`fib(10) = 55`). -/
def fibDef : AST.Definition :=
  [llvm-definition|
    define i32 @fib(i32 %n) {
    entry:
      br label %loop
    loop:
      %i = phi i32 [ 0, %entry ], [ %inext, %body ]
      %a = phi i32 [ 0, %entry ], [ %b, %body ]
      %b = phi i32 [ 1, %entry ], [ %sum, %body ]
      %done = icmp eq i32 %i, %n
      br i1 %done, label %exit, label %body
    body:
      %sum = add i32 %a, %b
      %inext = add i32 %i, 1
      br label %loop
    exit:
      ret i32 %a
    }
  ]

theorem cfg_loop_parallel_phi_fib10 :
    runDefinitionRet fibDef [.bv 32 (.value (10 : BitVec 32))] =
      .ok (.bv 32 (.value (55 : BitVec 32))) := by
  decide +kernel

/-- `switch` terminator test. -/
def switchDef : AST.Definition :=
  [llvm-definition|
    define i32 @sw(i32 %x) {
    entry:
      switch i32 %x, label %dflt [
        i32 0, label %c0
        i32 2, label %c2
      ]
    c0:
      ret i32 100
    c2:
      ret i32 200
    dflt:
      ret i32 999
    }
  ]

theorem cfg_switch_cases_and_default :
    runDefinitionRet switchDef [.bv 32 (.value (2 : BitVec 32))] = .ok (.bv 32 (.value (200 : BitVec 32))) ∧
    runDefinitionRet switchDef [.bv 32 (.value (7 : BitVec 32))] = .ok (.bv 32 (.value (999 : BitVec 32))) := by
  decide +kernel

/-- Recursive function call (`fact(5) = 120`) and indirect call through a function pointer. -/
def callsModule : AST.TopLevel := [llvm|
  define i32 @fact(i32 %n) {
  entry:
    %base = icmp sle i32 %n, 1
    br i1 %base, label %done, label %rec
  done:
    ret i32 1
  rec:
    %n1 = sub i32 %n, 1
    %recval = call i32 @fact(i32 %n1)
    %res = mul i32 %n, %recval
    ret i32 %res
  }

  define i32 @inc(i32 %x) {
  entry:
    %r = add i32 %x, 1
    ret i32 %r
  }

  define i32 @call_indirect(i32 %v) {
  entry:
    %slot = alloca ptr, align 8
    store ptr @inc, ptr %slot, align 8
    %fn = load ptr, ptr %slot, align 8
    %r = call i32 %fn(i32 %v)
    ret i32 %r
  }
]

theorem module_recursive_factorial_5 :
    runModuleFunction callsModule (.name "fact") [.bv 32 (.value (5 : BitVec 32))] =
      .ok (.bv 32 (.value (120 : BitVec 32))) := by
  decide +kernel

theorem module_indirect_function_pointer_call :
    runModuleFunction callsModule (.name "call_indirect") [.bv 32 (.value (41 : BitVec 32))] =
      .ok (.bv 32 (.value (42 : BitVec 32))) := by
  decide +kernel

/-- Aggregates (`insertvalue`/`extractvalue`) and vectors (`insertelement`/`extractelement`/`shufflevector`/lane-wise `add` & `select`). -/
theorem aggregates_and_vectors_eval :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %s0 = insertvalue { i32, [2 x i32] } zeroinitializer, i32 10, 0
        %s1 = insertvalue { i32, [2 x i32] } %s0, i32 20, 1, 1
        %a0 = extractvalue { i32, [2 x i32] } %s1, 0
        %a1 = extractvalue { i32, [2 x i32] } %s1, 1, 1
        %v1 = add <2 x i32> <i32 1, i32 2>, <i32 3, i32 4>
        %v2 = insertelement <2 x i32> %v1, i32 100, i32 0
        %sh = shufflevector <2 x i32> %v1, <2 x i32> %v2, <2 x i32> <i32 1, i32 2>
        %sel = select <2 x i1> <i1 true, i1 false>, <2 x i32> %sh, <2 x i32> %v1
        %e0 = extractelement <2 x i32> %sel, i32 0
        %e1 = extractelement <2 x i32> %sel, i32 1
        %t1 = add i32 %a0, %a1
        %t2 = add i32 %e0, %e1
        %res = add i32 %t1, %t2
        ret i32 %res
      }
    ] [] = .ok (.bv 32 (.value (42 : BitVec 32))) := by
  decide +kernel

/-- Integer bit-manipulation, saturating, and overflow intrinsics. -/
theorem integer_intrinsics_suite :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %a = call i32 @llvm.abs.i32(i32 -10, i1 false)
        %m = call i32 @llvm.smax.i32(i32 %a, i32 7)
        %lz = call i32 @llvm.ctlz.i32(i32 16, i1 false)
        %pop = call i32 @llvm.ctpop.i32(i32 7)
        %sat = call i8 @llvm.uadd.sat.i8(i8 200, i8 100)
        %sat32 = zext i8 %sat to i32
        %ov = call { i8, i1 } @llvm.sadd.with.overflow.i8(i8 120, i8 20)
        %ovFlag = extractvalue { i8, i1 } %ov, 1
        %ov32 = zext i1 %ovFlag to i32
        %s1 = add i32 %m, %lz
        %s2 = add i32 %s1, %pop
        %s3 = add i32 %s2, %sat32
        %s4 = add i32 %s3, %ov32
        ret i32 %s4
      }
    ] [] = .ok (.bv 32 (.value (296 : BitVec 32))) := by
  decide +kernel

end
