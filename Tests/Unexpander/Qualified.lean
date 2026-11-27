import Lean
import LeanNanoLlvm.AST

/-! Unexpander checks without `open LeanNanoLlvm.AST` (qualified constants). -/

/-! ### Unexpansion Without `open LeanNanoLlvm.AST` (Qualified Constants) -/

section
open scoped LeanNanoLlvm.AST.Syntax

/-- info: [llvm-instruction|call noundef i32 @helper(i32 noundef %a, ptr nonnull align 4 %p)] : LeanNanoLlvm.AST.Instruction -/
#guard_msgs in
#check [llvm-instruction| call noundef i32 @helper(i32 noundef %a, ptr nonnull align 4 %p)]

/-- info: [llvm-instruction|fneg nsz double -0.0] : LeanNanoLlvm.AST.Instruction -/
#guard_msgs in
#check [llvm-instruction| fneg nsz double -0.0]

/-- info: [llvm-instruction|fcmp oeq float %a, %b] : LeanNanoLlvm.AST.Instruction -/
#guard_msgs in
#check [llvm-instruction| fcmp oeq float %a, %b]

end

