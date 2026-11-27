/-!
# Kernel-reducible string helpers
-/

namespace LeanNanoLlvm

/-- Kernel-reducible string prefix check (avoids extern `ByteArray`-backed `String.startsWith`). -/
def strHasPrefix (s p : String) : Bool :=
  let rec go : List Char → List Char → Bool
    | _, [] => true
    | [], _ :: _ => false
    | c1 :: cs1, c2 :: cs2 => if c1 == c2 then go cs1 cs2 else false
  go s.toList p.toList

end LeanNanoLlvm
