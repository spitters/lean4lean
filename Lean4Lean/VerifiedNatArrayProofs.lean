/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean4Lean.VerifiedNat

/-!
# Value theorems for the `Array UInt64` routed operations

For each operation that `Lean4Lean.VerifiedNat` runs over the `Array UInt64`
carrier, the limb path on canonical operands equals the `Nat` operation, and
the compiled body `verifiedNat<Op>Impl` equals the logical body
`verifiedNat<Op>`.
-/

namespace VerifiedNat

theorem toNatA_landA_ofNatA (a b : Nat) : toNatA (landA (ofNatA a) (ofNatA b)) = a &&& b := by
  rw [toNatA_landA, toNatA_ofNatA, toNatA_ofNatA]

theorem toNatA_lorA_ofNatA (a b : Nat) : toNatA (lorA (ofNatA a) (ofNatA b)) = a ||| b := by
  rw [toNatA_lorA, toNatA_ofNatA, toNatA_ofNatA]

theorem toNatA_xorA_ofNatA (a b : Nat) : toNatA (xorA (ofNatA a) (ofNatA b)) = a ^^^ b := by
  rw [toNatA_xorA, toNatA_ofNatA, toNatA_ofNatA]

theorem toNatA_shiftLeftA_ofNatA (a k : Nat) : toNatA (shiftLeftA (ofNatA a) k) = a <<< k := by
  rw [toNatA_shiftLeftA, toNatA_ofNatA]

theorem toNatA_shiftRightA_ofNatA (a k : Nat) : toNatA (shiftRightA (ofNatA a) k) = a >>> k := by
  rw [toNatA_shiftRightA, toNatA_ofNatA]

theorem verifiedNatShiftLeftImpl_eq (a b : Nat) :
    verifiedNatShiftLeftImpl a b = verifiedNatShiftLeft a b := by
  unfold verifiedNatShiftLeftImpl verifiedNatShiftLeft
  split <;> simp only [toNatA_shiftLeftA_ofNatA]

theorem verifiedNatShiftRightImpl_eq (a b : Nat) :
    verifiedNatShiftRightImpl a b = verifiedNatShiftRight a b := by
  unfold verifiedNatShiftRightImpl verifiedNatShiftRight
  split <;> simp only [toNatA_shiftRightA_ofNatA]

theorem verifiedNatLandImpl_eq (a b : Nat) : verifiedNatLandImpl a b = verifiedNatLand a b := by
  unfold verifiedNatLandImpl verifiedNatLand
  split <;> simp only [toNatA_landA_ofNatA]

theorem verifiedNatLorImpl_eq (a b : Nat) : verifiedNatLorImpl a b = verifiedNatLor a b := by
  unfold verifiedNatLorImpl verifiedNatLor
  split <;> simp only [toNatA_lorA_ofNatA]

theorem verifiedNatXorImpl_eq (a b : Nat) : verifiedNatXorImpl a b = verifiedNatXor a b := by
  unfold verifiedNatXorImpl verifiedNatXor
  split <;> simp only [toNatA_xorA_ofNatA]

theorem verifiedNatBeqImpl_eq (a b : Nat) : verifiedNatBeqImpl a b = verifiedNatBeq a b := by
  unfold verifiedNatBeqImpl verifiedNatBeq
  split <;> simp only [beqA_ofNatA]

theorem verifiedNatBleImpl_eq (a b : Nat) : verifiedNatBleImpl a b = verifiedNatBle a b := by
  unfold verifiedNatBleImpl verifiedNatBle
  split <;> simp only [bleA_ofNatA]

end VerifiedNat
