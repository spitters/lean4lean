/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean4Lean.VerifiedNat

/-!
# Evaluation checks for the `Array UInt64` limb operations

Each `#eval` compares the limb operations of `Lean4Lean.VerifiedNatArray` and
`Lean4Lean.VerifiedNatArith`, and the routed `verifiedNat<Op>` functions, with
the `Nat` operations on a fixed set of operands (word boundaries, mixed limb
counts, 1000-bit values), shift counts across the limb boundary, powers with
exponents up to 1000, and power-of-two divisors. Each prints the list of failing cases,
which is empty when the operations agree.
-/

namespace VerifiedNat.Test

/-- Operands covering zero, the word boundaries and mixed limb counts. -/
def operands : List Nat :=
  [0, 1, 2, 12345, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
   2 ^ 127 + 3, 2 ^ 128 - 1, 2 ^ 128, 3 ^ 90, 2 ^ 191 + 2 ^ 64 + 5,
   2 ^ 1000 - 1, 2 ^ 1000, 7 ^ 300, 2 ^ 1000 - 1 - 2 ^ 500]

/-- Shift counts across the limb boundary. -/
def shiftCounts : List Nat := [0, 1, 63, 64, 65, 127, 128, 1000]

/-- Operand pairs on which a binary operation disagrees with its reference. -/
def failures {α : Type} [BEq α] (f g : Nat → Nat → α) : List (Nat × Nat) :=
  operands.flatMap fun a => (operands.filter fun b => f a b != g a b).map (a, ·)

/-- Operand/count pairs on which a shift disagrees with its reference. -/
def shiftFailures (f g : Nat → Nat → Nat) : List (Nat × Nat) :=
  operands.flatMap fun a => (shiftCounts.filter fun k => f a k != g a k).map (a, ·)

#eval operands.filter fun n => toNatA (ofNatA n) != n
#eval operands.filter fun n => (ofNatA n).back? == some 0

#eval failures (fun a b => toNatA (landA (ofNatA a) (ofNatA b))) (· &&& ·)
#eval failures (fun a b => toNatA (lorA (ofNatA a) (ofNatA b))) (· ||| ·)
#eval failures (fun a b => toNatA (xorA (ofNatA a) (ofNatA b))) (· ^^^ ·)
#eval failures (fun a b => landA (ofNatA a) (ofNatA b)) (fun a b => ofNatA (a &&& b))
#eval failures (fun a b => xorA (ofNatA a) (ofNatA b)) (fun a b => ofNatA (a ^^^ b))
#eval failures (fun a b => cmpA (ofNatA a) (ofNatA b)) compare
#eval failures (fun a b => beqA (ofNatA a) (ofNatA b)) Nat.beq
#eval failures (fun a b => bleA (ofNatA a) (ofNatA b)) Nat.ble

#eval shiftFailures (fun a k => toNatA (shiftLeftA (ofNatA a) k)) (· <<< ·)
#eval shiftFailures (fun a k => toNatA (shiftRightA (ofNatA a) k)) (· >>> ·)
#eval shiftFailures (fun a k => (shiftLeftA (ofNatA a) k).size) (fun a k => (ofNatA (a <<< k)).size)
#eval shiftFailures (fun a k => (shiftRightA (ofNatA a) k).size)
  (fun a k => (ofNatA (a >>> k)).size)

#eval failures verifiedNatLand (· &&& ·)
#eval failures verifiedNatLor (· ||| ·)
#eval failures verifiedNatXor (· ^^^ ·)
#eval failures verifiedNatBeq Nat.beq
#eval failures verifiedNatBle Nat.ble
#eval shiftFailures verifiedNatShiftLeft (· <<< ·)
#eval shiftFailures verifiedNatShiftRight (· >>> ·)

/-! ### Addition, subtraction, multiplication, powers, power-of-two division -/

/-- Operands for the arithmetic checks. -/
def arithOperands : List Nat :=
  [0, 1, 2 ^ 32 - 1, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 100 + 7, 2 ^ 128 + 2 ^ 64 - 1,
   2 ^ 1000 - 1, 3 ^ 500]

/-- Pairs from `xs × ys` on which `f` disagrees with `g`. -/
def failuresOn {α : Type} [BEq α] (xs ys : List Nat) (f g : Nat → Nat → α) :
    List (Nat × Nat) :=
  xs.flatMap fun a => (ys.filter fun b => f a b != g a b).map (a, ·)

#eval failuresOn arithOperands arithOperands
  (fun a b => toNatA (addA (ofNatA a) (ofNatA b))) (· + ·)
#eval failuresOn arithOperands arithOperands
  (fun a b => toNatA (subA (ofNatA a) (ofNatA b))) (· - ·)
#eval failuresOn arithOperands arithOperands
  (fun a b => toNatA (mulA (ofNatA a) (ofNatA b))) (· * ·)
#eval failuresOn arithOperands arithOperands
  (fun a b => addA (ofNatA a) (ofNatA b)) (fun a b => ofNatA (a + b))
#eval failuresOn arithOperands arithOperands
  (fun a b => subA (ofNatA a) (ofNatA b)) (fun a b => ofNatA (a - b))
#eval failuresOn arithOperands arithOperands
  (fun a b => mulA (ofNatA a) (ofNatA b)) (fun a b => ofNatA (a * b))
#eval failuresOn arithOperands arithOperands verifiedNatAdd (· + ·)
#eval failuresOn arithOperands arithOperands verifiedNatSub (· - ·)
#eval failuresOn arithOperands arithOperands verifiedNatMul (· * ·)

/-- Bases for the power checks with exponents up to 1000. -/
def powBases : List Nat := [0, 1, 2, 3]
/-- Exponents for the power checks. -/
def powExps : List Nat := [0, 1, 2, 63, 64, 100, 1000]
/-- Exponents for the two-limb base `2 ^ 64 + 1`, whose 1000th power has 1000
    dense limbs. -/
def powExpsWide : List Nat := [0, 1, 2, 63, 64, 100]

#eval failuresOn powBases powExps verifiedNatPow (· ^ ·)
#eval failuresOn powBases powExps
  (fun a b => toNatA (powA (ofNatA a) b (ofNatA 1))) (· ^ ·)
#eval failuresOn [2 ^ 64 + 1] powExpsWide verifiedNatPow (· ^ ·)
#eval failuresOn [2 ^ 64 + 1] powExpsWide
  (fun a b => toNatA (powA (ofNatA a) b (ofNatA 1))) (· ^ ·)

/-- Power-of-two divisors. -/
def pow2Divisors : List Nat := [1, 2, 2 ^ 63, 2 ^ 64, 2 ^ 100, 2 ^ 1000]

#eval failuresOn arithOperands pow2Divisors verifiedNatDiv (· / ·)
#eval failuresOn arithOperands pow2Divisors verifiedNatMod (· % ·)
#eval failuresOn arithOperands [3, 2 ^ 64 + 1] verifiedNatDiv (· / ·)
#eval failuresOn arithOperands [3, 2 ^ 64 + 1] verifiedNatMod (· % ·)

end VerifiedNat.Test
