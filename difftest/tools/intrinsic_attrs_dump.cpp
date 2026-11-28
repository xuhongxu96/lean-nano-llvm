// Print `<intrinsic base name>\t<function attributes>` for every intrinsic ID, as LLVM's
// AsmWriter prints an attribute group (`AttributeSet::getAsString(true)`).
#include "llvm/IR/Attributes.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;
int main() {
  LLVMContext C;
  for (unsigned id = 1; id < Intrinsic::num_intrinsics; ++id) {
    AttributeSet AS = Intrinsic::getFnAttributes(C, (Intrinsic::ID)id);
    outs() << Intrinsic::getBaseName((Intrinsic::ID)id) << "\t" << AS.getAsString(true) << "\n";
  }
}
