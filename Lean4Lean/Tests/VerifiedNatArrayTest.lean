/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean4Lean.VerifiedNat

/-!
# Evaluation checks for the `Array UInt64` limb operations

Each `#eval` compares the limb operations of `Lean4Lean.VerifiedNatArray`, and
the routed `verifiedNat<Op>` functions, with the `Nat` operations on a fixed
set of operands (word boundaries, mixed limb counts, a 1000-bit value) and
shift counts `0, 1, 63, 64, 65, 1000`. Each prints the list of failing cases,
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

end VerifiedNat.Test
