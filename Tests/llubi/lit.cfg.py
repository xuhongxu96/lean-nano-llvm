# lit configuration: run LLVM's llubi test suite (llvm/test/tools/llubi) unmodified, with `llubi`
# substituted by lean-nano-llvm's llubi-compatible frontend (`lean-nano-llvm llubi`).
#
# Parameters (`lit --param name=value`) or environment variables:
#   llubi_test_dir  / LLUBI_TEST_DIR   directory containing the llubi `.ll` tests (required)
#   lean_nano_llvm  / LEAN_NANO_LLVM   frontend binary (default: .lake/build/bin/lean-nano-llvm)
#   filecheck       / FILECHECK        FileCheck binary (default: `FileCheck` or `filecheck` on PATH)
import os
import shutil
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from llubi_format import LlubiTest  # noqa: E402

repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def param(name, env, default=None):
    return lit_config.params.get(name, os.environ.get(env, default))


test_dir = param("llubi_test_dir", "LLUBI_TEST_DIR")
if not test_dir or not os.path.isdir(test_dir):
    lit_config.fatal("set --param llubi_test_dir=<llvm-project>/llvm/test/tools/llubi")

binary = param("lean_nano_llvm", "LEAN_NANO_LLVM",
               os.path.join(repo_root, ".lake", "build", "bin", "lean-nano-llvm"))
filecheck = param("filecheck", "FILECHECK",
                  shutil.which("FileCheck") or shutil.which("filecheck"))
if not filecheck:
    lit_config.fatal("FileCheck not found (install LLVM's FileCheck or `pip install filecheck`)")


xfail_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "xfail.txt")
xfails = set()
if os.path.exists(xfail_path):
    with open(xfail_path) as f:
        xfails = {l.split("#")[0].strip() for l in f} - {""}

config.name = "llubi-lean-nano-llvm"
config.test_format = LlubiTest(xfails)
config.suffixes = [".ll"]
config.test_source_root = test_dir
config.test_exec_root = os.path.join(repo_root, ".lake", "build", "llubi-tests")
config.substitutions.append((r"(?<![\w/.-])llubi\b", f'"{binary}" llubi'))
config.substitutions.append((r"(?<![\w/.-])FileCheck\b", f'"{filecheck}"'))
