/-!
# Hexadecimal formatting

The hexadecimal renderings shared by diagnostics, the IR printer and the `llubi` frontend.
Digits are produced by `Nat.toDigits`, so all of these reduce in the kernel.
-/

namespace LeanNanoLlvm.Hex

/-- `n` in lower-case hexadecimal, without prefix. -/
def lower (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

/-- `n` in upper-case hexadecimal, without prefix. -/
def upper (n : Nat) : String :=
  String.ofList ((Nat.toDigits 16 n).map Char.toUpper)

/-- Left-pad `s` with `'0'` to `width` characters. -/
def zeroPad (width : Nat) (s : String) : String :=
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- `n` in upper-case hexadecimal, zero-padded to `width` digits. -/
def upperPadded (width n : Nat) : String :=
  zeroPad width (upper n)

/-- `n` in lower-case hexadecimal, zero-padded to `width` digits. -/
def lowerPadded (width n : Nat) : String :=
  zeroPad width (lower n)

end LeanNanoLlvm.Hex
