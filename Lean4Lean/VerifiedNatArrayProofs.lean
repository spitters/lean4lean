/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE-MIT.
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

theorem toNatA_addA_ofNatA (a b : Nat) : toNatA (addA (ofNatA a) (ofNatA b)) = a + b := by
  rw [toNatA_addA, toNatA_ofNatA, toNatA_ofNatA]

theorem toNatA_subA_ofNatA (a b : Nat) : toNatA (subA (ofNatA a) (ofNatA b)) = a - b := by
  rw [toNatA_subA, toNatA_ofNatA, toNatA_ofNatA]

theorem toNatA_mulA_ofNatA (a b : Nat) : toNatA (mulA (ofNatA a) (ofNatA b)) = a * b := by
  rw [toNatA_mulA, toNatA_ofNatA, toNatA_ofNatA]

theorem toNatA_powA_ofNatA (a b : Nat) : toNatA (powA (ofNatA a) b (ofNatA 1)) = a ^ b := by
  rw [toNatA_powA, toNatA_ofNatA, toNatA_ofNatA, Nat.one_mul]

theorem verifiedNatAddImpl_eq (a b : Nat) : verifiedNatAddImpl a b = verifiedNatAdd a b := by
  unfold verifiedNatAddImpl verifiedNatAdd
  split <;> simp only [toNatA_addA_ofNatA]

theorem verifiedNatSubImpl_eq (a b : Nat) : verifiedNatSubImpl a b = verifiedNatSub a b := by
  unfold verifiedNatSubImpl verifiedNatSub
  split <;> simp only [toNatA_subA_ofNatA]

theorem verifiedNatMulImpl_eq (a b : Nat) : verifiedNatMulImpl a b = verifiedNatMul a b := by
  unfold verifiedNatMulImpl verifiedNatMul
  split <;> simp only [toNatA_mulA_ofNatA]

theorem verifiedNatPowImpl_eq (a b : Nat) : verifiedNatPowImpl a b = verifiedNatPow a b := by
  unfold verifiedNatPowImpl verifiedNatPow
  by_cases hb : b = 0
  · simp [hb]
  rw [if_neg hb]
  by_cases ha : a < 2
  · rw [if_pos ha]
    rcases (show a = 0 ∨ a = 1 by omega) with h | h <;> subst h
    · exact (Nat.zero_pow (Nat.pos_of_ne_zero hb)).symm
    · exact (Nat.one_pow b).symm
  rw [if_neg ha]
  by_cases h2 : a = 2
  · subst h2
    rw [if_pos rfl]
    split
    · exact Nat.one_shiftLeft b
    · rw [toNatA_shiftLeftA_ofNatA, Nat.one_shiftLeft]
  rw [if_neg h2]
  split
  · rfl
  · exact toNatA_powA_ofNatA a b

theorem eq_two_pow_log2 {b : Nat} (h0 : b ≠ 0) (hp : b &&& (b - 1) = 0) : b = 2 ^ b.log2 := by
  obtain ⟨k, hk⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo h0).mp hp
  rw [hk, Nat.log2_two_pow]

/-- On a nonzero power-of-two divisor, the compiled quotient equals `a / b`. -/
theorem verifiedNatDivImpl_eq_of_pow2 (a b : Nat) (h0 : b ≠ 0) (hp : b &&& (b - 1) = 0) :
    verifiedNatDivImpl a b = verifiedNatDiv a b := by
  unfold verifiedNatDivImpl verifiedNatDiv
  rw [if_neg h0, if_pos hp]
  have hb := eq_two_pow_log2 h0 hp
  split
  · rw [Nat.shiftRight_eq_div_pow, ← hb]
  · rw [toNatA_shiftRightA_ofNatA, Nat.shiftRight_eq_div_pow, ← hb]

/-- On a nonzero power-of-two divisor, the compiled remainder equals `a % b`. -/
theorem verifiedNatModImpl_eq_of_pow2 (a b : Nat) (h0 : b ≠ 0) (hp : b &&& (b - 1) = 0) :
    verifiedNatModImpl a b = verifiedNatMod a b := by
  unfold verifiedNatModImpl verifiedNatMod
  rw [if_neg h0, if_pos hp]
  have hb := eq_two_pow_log2 h0 hp
  split
  · rw [hb, Nat.and_two_pow_sub_one_eq_mod]
  · rw [toNatA_landA_ofNatA, hb, Nat.and_two_pow_sub_one_eq_mod]

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
