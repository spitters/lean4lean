/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean4Lean.VerifiedNatArray

/-!
# Addition, subtraction, multiplication and powers over `Array UInt64`

Limb loops on the little-endian `Array UInt64` carrier of
`Lean4Lean.VerifiedNatArray`:

* `addA`: limb-wise add with a `UInt64` carry;
* `subA`: limb-wise subtract with a `UInt64` borrow, returning `#[]` when the
  final borrow is set (truncated subtraction);
* `mulA`: schoolbook multiplication into a zero-initialized result of size
  `x.size + y.size`, updated in place, with the double-word limb product
  computed from four `32 × 32`-bit `UInt64` products;
* `powA`: square-and-multiply over `mulA`.

Each operation carries a value theorem stated through `toNatA`, for all
arrays. The loop invariants are stated through `valN a n`, the value of the
`n` low limbs of `a`.
-/

namespace VerifiedNat

/-! ## Value of a limb prefix -/

/-- The value of the limbs of `a` below index `n`, least significant first. -/
def valN (a : Array UInt64) : Nat → Nat
  | 0 => 0
  | n + 1 => valN a n + (a.getD n 0).toNat * 2 ^ (64 * n)

theorem valN_congr {a b : Array UInt64} (n : Nat) (h : ∀ j, j < n → a.getD j 0 = b.getD j 0) :
    valN a n = valN b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [valN]
    rw [ih fun j hj => h j (by omega), h n (by omega)]

theorem valN_lt (a : Array UInt64) (n : Nat) : valN a n < 2 ^ (64 * n) := by
  induction n with
  | zero => simp [valN]
  | succ n ih =>
    simp only [valN]
    have hl := (a.getD n 0).toNat_lt
    rw [show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add]
    have : ((a.getD n 0).toNat + 1) * 2 ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) :=
      Nat.mul_le_mul_right _ hl
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm (2 ^ (64 * n))]
    omega

theorem toNatA_eq_valN_add (x : Array UInt64) (n : Nat) :
    toNatA x = valN x n + (toNatA x >>> (64 * n)) * 2 ^ (64 * n) := by
  induction n with
  | zero => simp [valN]
  | succ n ih =>
    conv => lhs; rw [ih, shiftRight_limb x n]
    simp only [valN]
    rw [show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add]
    generalize toNatA x >>> (64 * n + 64) = T
    generalize (x.getD n 0).toNat = L
    generalize 2 ^ (64 * n) = P
    rw [Nat.add_mul, Nat.add_assoc, Nat.add_comm (T * 2 ^ 64 * P), Nat.mul_assoc,
      Nat.mul_comm (2 ^ 64) P]

theorem toNatA_eq_valN (x : Array UInt64) {n : Nat} (h : x.size ≤ n) : toNatA x = valN x n := by
  have hs : toNatA x >>> (64 * n) = 0 :=
    Nat.shiftRight_eq_zero _ _
      (Nat.lt_of_lt_of_le (toNatA_lt x) (Nat.pow_le_pow_right (by decide) (by omega)))
  have := toNatA_eq_valN_add x n
  rw [hs, Nat.zero_mul, Nat.add_zero] at this
  exact this

theorem getD_push (acc : Array UInt64) (v : UInt64) (j : Nat) :
    (acc.push v).getD j 0 = if j = acc.size then v else acc.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> simp

theorem valN_push (acc : Array UInt64) (v : UInt64) :
    valN (acc.push v) (acc.size + 1) = valN acc acc.size + v.toNat * 2 ^ (64 * acc.size) := by
  simp only [valN, getD_push, if_pos]
  congr 1
  exact valN_congr _ fun j hj => by rw [getD_push, if_neg (by omega)]

theorem getD_set! (r : Array UInt64) (k : Nat) (v : UInt64) (j : Nat) :
    (r.set! k v).getD j 0 = if j = k ∧ k < r.size then v else r.getD j 0 := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h1 : j = k
  · subst h1
    by_cases h2 : j < r.size
    · simp [h2]
    · simp [h2]
  · simp [h1, Ne.symm h1]

theorem valN_set! (r : Array UInt64) {k : Nat} (v : UInt64) (hk : k < r.size) (N : Nat) :
    valN (r.set! k v) N + (if k < N then (r.getD k 0).toNat * 2 ^ (64 * k) else 0) =
      valN r N + (if k < N then v.toNat * 2 ^ (64 * k) else 0) := by
  induction N with
  | zero => simp [valN]
  | succ N ih =>
    simp only [valN, getD_set!]
    by_cases hN : k < N
    · have h1 : k < N + 1 := by omega
      have h2 : ¬ (N = k ∧ k < r.size) := by omega
      simp only [hN, h1, h2, if_true, if_false] at ih ⊢
      omega
    · by_cases hkN : k = N
      · subst hkN
        have h1 : k < k + 1 := by omega
        have h2 : k = k ∧ k < r.size := ⟨rfl, hk⟩
        rw [if_pos h2]
        simp only [hN, h1, if_true, if_false] at ih ⊢
        omega
      · have h1 : ¬ k < N + 1 := by omega
        have h2 : ¬ (N = k ∧ k < r.size) := by omega
        simp only [hN, h1, h2, if_false] at ih ⊢
        omega

/-! ## Word operations -/

/-- Sum of two limbs and a carry: the low limb and the carry out. -/
@[inline] def addc (a b c : UInt64) : UInt64 × UInt64 :=
  let s := a + b
  let t := s + c
  (t, (if s < a then 1 else 0) + (if t < s then 1 else 0))

theorem addc_spec (a b c : UInt64) :
    (addc a b c).1.toNat + (addc a b c).2.toNat * 2 ^ 64 = a.toNat + b.toNat + c.toNat ∧
      (c.toNat ≤ 1 → (addc a b c).2.toNat ≤ 1) := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  simp only [addc]
  split <;> split <;>
    simp_all [UInt64.toNat_add, UInt64.lt_iff_toNat_lt] <;> omega

/-- Difference of two limbs and a borrow: the low limb and the borrow out. -/
@[inline] def subb (a b c : UInt64) : UInt64 × UInt64 :=
  let d := a - b
  let t := d - c
  (t, (if a < b then 1 else 0) + (if d < c then 1 else 0))

theorem subb_spec (a b c : UInt64) (hc : c.toNat ≤ 1) :
    a.toNat + (subb a b c).2.toNat * 2 ^ 64 = (subb a b c).1.toNat + b.toNat + c.toNat ∧
      (subb a b c).2.toNat ≤ 1 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [subb]
  split <;> split <;>
    simp_all [UInt64.toNat_sub, UInt64.lt_iff_toNat_lt] <;> omega

/-- The double-word product `a * b` as `(high limb, low limb)`. The high limb is
    assembled from the four `32 × 32`-bit products of the halves of `a` and `b`;
    the low limb is the wrapping product. -/
@[inline] def mulWide (a b : UInt64) : UInt64 × UInt64 :=
  let m : UInt64 := 0xFFFFFFFF
  let a0 := a &&& m
  let a1 := a >>> 32
  let b0 := b &&& m
  let b1 := b >>> 32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := (p00 >>> 32) + (p01 &&& m) + (p10 &&& m)
  (p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32), a * b)

theorem toNat_and_mask (a : UInt64) : (a &&& 0xFFFFFFFF).toNat = a.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_shr32 (a : UInt64) : (a >>> 32).toNat = a.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
    Nat.shiftRight_eq_div_pow]

theorem toNat_mul_of_lt {a b : UInt64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h]

theorem half_mul_lt {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) : x * y < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)) (by decide)

theorem half_mul_le {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    x * y ≤ 18446744065119617025 :=
  Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)) (by decide)

theorem mulWide_spec (a b : UInt64) :
    (mulWide a b).1.toNat * 2 ^ 64 + (mulWide a b).2.toNat = a.toNat * b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [mulWide]
  generalize ea : a.toNat = A at *
  generalize eb : b.toNat = B at *
  have hA0 : (a &&& 0xFFFFFFFF).toNat = A % 2 ^ 32 := by rw [toNat_and_mask, ea]
  have hA1 : (a >>> 32).toNat = A / 2 ^ 32 := by rw [toNat_shr32, ea]
  have hB0 : (b &&& 0xFFFFFFFF).toNat = B % 2 ^ 32 := by rw [toNat_and_mask, eb]
  have hB1 : (b >>> 32).toNat = B / 2 ^ 32 := by rw [toNat_shr32, eb]
  have lA0 : A % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have lB0 : B % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have lA1 : A / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by simpa using ha)
  have lB1 : B / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by simpa using hb)
  generalize a &&& 0xFFFFFFFF = a0 at *
  generalize a >>> 32 = a1 at *
  generalize b &&& 0xFFFFFFFF = b0 at *
  generalize b >>> 32 = b1 at *
  have hA : A = A / 2 ^ 32 * 2 ^ 32 + A % 2 ^ 32 := by omega
  have hB : B = B / 2 ^ 32 * 2 ^ 32 + B % 2 ^ 32 := by omega
  generalize A % 2 ^ 32 = A0 at *
  generalize A / 2 ^ 32 = A1 at *
  generalize B % 2 ^ 32 = B0 at *
  generalize B / 2 ^ 32 = B1 at *
  subst hA hB
  have p00 : (a0 * b0).toNat = A0 * B0 := by
    rw [toNat_mul_of_lt] <;> rw [hA0, hB0]; exact half_mul_lt lA0 lB0
  have p01 : (a0 * b1).toNat = A0 * B1 := by
    rw [toNat_mul_of_lt] <;> rw [hA0, hB1]; exact half_mul_lt lA0 lB1
  have p10 : (a1 * b0).toNat = A1 * B0 := by
    rw [toNat_mul_of_lt] <;> rw [hA1, hB0]; exact half_mul_lt lA1 lB0
  have p11 : (a1 * b1).toNat = A1 * B1 := by
    rw [toNat_mul_of_lt] <;> rw [hA1, hB1]; exact half_mul_lt lA1 lB1
  have q00 := half_mul_le lA0 lB0
  have q01 := half_mul_le lA0 lB1
  have q10 := half_mul_le lA1 lB0
  have q11 := half_mul_le lA1 lB1
  have hAB : (A1 * 2 ^ 32 + A0) * (B1 * 2 ^ 32 + B0) =
      A1 * B1 * 2 ^ 64 + A0 * B1 * 2 ^ 32 + A1 * B0 * 2 ^ 32 + A0 * B0 := by
    grind
  simp only [UInt64.toNat_add, UInt64.toNat_mul, toNat_shr32, toNat_and_mask, p00, p01, p10, p11]
  rw [ea, eb, hAB]
  generalize A0 * B0 = P00 at *
  generalize A0 * B1 = P01 at *
  generalize A1 * B0 = P10 at *
  generalize A1 * B1 = P11 at *
  omega

/-- `a * b + r + c` as `(low limb, high limb)`. -/
@[inline] def mulAddc (a b r c : UInt64) : UInt64 × UInt64 :=
  let p := mulWide a b
  let s := addc p.2 r c
  (s.1, p.1 + s.2)

theorem mulAddc_spec (a b r c : UInt64) :
    (mulAddc a b r c).1.toNat + (mulAddc a b r c).2.toNat * 2 ^ 64 =
      a.toNat * b.toNat + r.toNat + c.toNat := by
  have hw := mulWide_spec a b
  have hs := (addc_spec (mulWide a b).2 r c).1
  have hP : a.toNat * b.toNat ≤ 340282366920938463426481119284349108225 :=
    Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt a.toNat_lt) (Nat.le_pred_of_lt b.toNat_lt))
      (by decide)
  have hr := r.toNat_lt
  have hc := c.toNat_lt
  have hl := (addc (mulWide a b).2 r c).1.toNat_lt
  have hL := (mulWide a b).2.toNat_lt
  simp only [mulAddc, UInt64.toNat_add]
  generalize a.toNat * b.toNat = P at *
  generalize (mulWide a b).1.toNat = H at *
  generalize (mulWide a b).2.toNat = L at *
  generalize (addc (mulWide a b).2 r c).1.toNat = T at *
  generalize (addc (mulWide a b).2 r c).2.toNat = C at *
  generalize r.toNat = R at *
  generalize c.toNat = C0 at *
  have hHC : H + C < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hHC, Nat.add_mul, ← hw, ← Nat.add_assoc, Nat.add_comm T,
    Nat.add_assoc (H * 2 ^ 64), hs]
  omega

/-! ## Addition -/

/-- Limbs `i, …, n - 1` of `x + y` with carry `c`, pushed onto `acc`, followed
    by the final carry limb. -/
def addLoop (x y : Array UInt64) (n i : Nat) (c : UInt64) (acc : Array UInt64) :
    Array UInt64 :=
  if i < n then
    let p := addc (x.getD i 0) (y.getD i 0) c
    addLoop x y n (i + 1) p.2 (acc.push p.1)
  else acc.push c
termination_by n - i

/-- Sum of two limb arrays, normalized. -/
def addA (x y : Array UInt64) : Array UInt64 :=
  let n := max x.size y.size
  normA (addLoop x y n 0 0 (Array.emptyWithCapacity (n + 1)))

theorem addLoop_spec (x y : Array UInt64) (n i : Nat) (c : UInt64) (acc : Array UInt64)
    (hi : i ≤ n) (hs : acc.size = i) (hc : c.toNat ≤ 1)
    (hv : valN acc i + c.toNat * 2 ^ (64 * i) = valN x i + valN y i) :
    (addLoop x y n i c acc).size = n + 1 ∧
      valN (addLoop x y n i c acc) (n + 1) = valN x n + valN y n := by
  fun_induction addLoop x y n i c acc with
  | case1 i c acc hin p ih =>
    have hp := addc_spec (x.getD i 0) (y.getD i 0) c
    apply ih (by omega) (by simp [hs]) (hp.2 hc)
    have e := valN_push acc p.1
    rw [hs] at e
    rw [e]
    simp only [valN, p]
    rw [show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add]
    generalize 2 ^ (64 * i) = Q at *
    have h1 : (addc (x.getD i 0) (y.getD i 0) c).2.toNat * (Q * 2 ^ 64) =
      (addc (x.getD i 0) (y.getD i 0) c).2.toNat * 2 ^ 64 * Q := by
      rw [Nat.mul_comm Q, Nat.mul_assoc]
    rw [h1, Nat.add_assoc, ← Nat.add_mul, hp.1, Nat.add_mul, Nat.add_mul]
    omega
  | case2 i c acc hin =>
    have hin' : i = n := by omega
    subst hin'
    refine ⟨by simp [hs], ?_⟩
    have e := valN_push acc c
    rw [hs] at e
    rw [e, hv]

theorem toNatA_normA (x : Array UInt64) : toNatA (normA x) = toNatA x :=
  Nat.eq_of_testBit_eq fun j => by rw [testBit_toNatA, testBit_toNatA, limbBit_normA]

theorem toNatA_addA (x y : Array UInt64) : toNatA (addA x y) = toNatA x + toNatA y := by
  have h := addLoop_spec x y (max x.size y.size) 0 0
    (Array.emptyWithCapacity (max x.size y.size + 1)) (Nat.zero_le _) (by simp) (by decide)
    (by simp [valN])
  rw [addA, toNatA_normA, toNatA_eq_valN _ (Nat.le_of_eq h.1), h.2,
    toNatA_eq_valN x (Nat.le_max_left _ _), toNatA_eq_valN y (Nat.le_max_right _ _)]

/-! ## Subtraction -/

/-- Limbs `i, …, n - 1` of `x - y` with borrow `c`, pushed onto `acc`, and the
    final borrow. -/
def subLoop (x y : Array UInt64) (n i : Nat) (c : UInt64) (acc : Array UInt64) :
    Array UInt64 × UInt64 :=
  if i < n then
    let p := subb (x.getD i 0) (y.getD i 0) c
    subLoop x y n (i + 1) p.2 (acc.push p.1)
  else (acc, c)
termination_by n - i

/-- Truncated difference of two limb arrays: the limb-wise difference with
    borrow, normalized, or `#[]` when the final borrow is set. -/
def subA (x y : Array UInt64) : Array UInt64 :=
  let n := max x.size y.size
  let r := subLoop x y n 0 0 (Array.emptyWithCapacity n)
  if r.2 = 0 then normA r.1 else #[]

theorem subLoop_spec (x y : Array UInt64) (n i : Nat) (c : UInt64) (acc : Array UInt64)
    (hi : i ≤ n) (hs : acc.size = i) (hc : c.toNat ≤ 1)
    (hv : valN x i + c.toNat * 2 ^ (64 * i) = valN acc i + valN y i) :
    (subLoop x y n i c acc).1.size = n ∧ (subLoop x y n i c acc).2.toNat ≤ 1 ∧
      valN x n + (subLoop x y n i c acc).2.toNat * 2 ^ (64 * n) =
        valN (subLoop x y n i c acc).1 n + valN y n := by
  fun_induction subLoop x y n i c acc with
  | case1 i c acc hin p ih =>
    have hp := subb_spec (x.getD i 0) (y.getD i 0) c hc
    apply ih (by omega) (by simp [hs]) hp.2
    have e := valN_push acc p.1
    rw [hs] at e
    rw [e]
    simp only [valN, p]
    rw [show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add]
    generalize 2 ^ (64 * i) = Q at *
    have h1 : (subb (x.getD i 0) (y.getD i 0) c).2.toNat * (Q * 2 ^ 64) =
      (subb (x.getD i 0) (y.getD i 0) c).2.toNat * 2 ^ 64 * Q := by
      rw [Nat.mul_comm Q, Nat.mul_assoc]
    have h2 := congrArg (· * Q) hp.1
    simp only [Nat.add_mul] at h2
    rw [h1]
    omega
  | case2 i c acc hin =>
    have hin' : i = n := by omega
    subst hin'
    exact ⟨hs, hc, hv⟩

theorem toNatA_subA (x y : Array UInt64) : toNatA (subA x y) = toNatA x - toNatA y := by
  have h := subLoop_spec x y (max x.size y.size) 0 0
    (Array.emptyWithCapacity (max x.size y.size)) (Nat.zero_le _) (by simp) (by decide)
    (by simp [valN])
  have hx := toNatA_eq_valN x (Nat.le_max_left x.size y.size)
  have hy := toNatA_eq_valN y (Nat.le_max_right x.size y.size)
  have hlt := valN_lt (subLoop x y (max x.size y.size) 0 0
    (Array.emptyWithCapacity (max x.size y.size))).1 (max x.size y.size)
  have hxl := valN_lt x (max x.size y.size)
  unfold subA
  simp only
  generalize subLoop x y (max x.size y.size) 0 0
    (Array.emptyWithCapacity (max x.size y.size)) = r at *
  obtain ⟨h1, h2, h3⟩ := h
  rw [hx, hy]
  generalize 2 ^ (64 * max x.size y.size) = Q at *
  split
  · rename_i h0
    rw [toNatA_normA, toNatA_eq_valN _ (Nat.le_of_eq h1)]
    rw [h0] at h3
    simp only [UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero] at h3
    omega
  · rename_i h0
    have : r.2.toNat = 1 := by
      have : r.2.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
      omega
    rw [this, Nat.one_mul] at h3
    simp only [toNatA, Array.size_empty, toNatRange]
    omega

/-! ## Multiplication -/

/-- Add `xi * y` into `r` at limb offset `i`: limbs `j, …, m - 1` with carry `c`,
    then the final carry written at index `i + m`. -/
def mulRow (xi : UInt64) (y : Array UInt64) (m i j : Nat) (c : UInt64) (r : Array UInt64) :
    Array UInt64 :=
  if j < m then
    let p := mulAddc xi (y.getD j 0) (r.getD (i + j) 0) c
    mulRow xi y m i (j + 1) p.2 (r.set! (i + j) p.1)
  else r.set! (i + m) c
termination_by m - j

/-- Rows `i, …, n - 1` of the schoolbook product of `x` and `y`, accumulated in `r`. -/
def mulRows (x y : Array UInt64) (n m i : Nat) (r : Array UInt64) : Array UInt64 :=
  if i < n then
    let xi := x.getD i 0
    mulRows x y n m (i + 1) (if xi = 0 then r else mulRow xi y m i 0 0 r)
  else r
termination_by n - i

/-- Schoolbook product of two limb arrays, normalized. -/
def mulA (x y : Array UInt64) : Array UInt64 :=
  if x.size = 0 || y.size = 0 then #[]
  else normA (mulRows x y x.size y.size 0 (Array.replicate (x.size + y.size) 0))

theorem size_set! (r : Array UInt64) (k : Nat) (v : UInt64) : (r.set! k v).size = r.size := by
  simp [Array.set!_eq_setIfInBounds]

theorem mulRow_spec (xi : UInt64) (y : Array UInt64) (m i N V0 : Nat) (j : Nat) (c : UInt64)
    (r : Array UInt64) (hj : j ≤ m) (hN : r.size = N) (him : i + m < N)
    (hz : ∀ k, i + m ≤ k → r.getD k 0 = 0)
    (hv : valN r N + c.toNat * 2 ^ (64 * (i + j)) = V0 + xi.toNat * valN y j * 2 ^ (64 * i)) :
    (mulRow xi y m i j c r).size = N ∧
      (∀ k, i + m < k → (mulRow xi y m i j c r).getD k 0 = 0) ∧
      valN (mulRow xi y m i j c r) N = V0 + xi.toNat * valN y m * 2 ^ (64 * i) := by
  fun_induction mulRow xi y m i j c r with
  | case1 j c r hjm p ih =>
    have hw := mulAddc_spec xi (y.getD j 0) (r.getD (i + j) 0) c
    have hs := valN_set! r p.1 (k := i + j) (by omega) N
    rw [if_pos (by omega), if_pos (by omega)] at hs
    apply ih (by omega) (by rw [size_set!, hN])
    · intro k hk
      rw [getD_set!, if_neg (by omega), hz k hk]
    · simp only [valN]
      rw [show 64 * (i + (j + 1)) = 64 * (i + j) + 64 by omega, Nat.pow_add,
        show 2 ^ (64 * (i + j)) = 2 ^ (64 * j) * 2 ^ (64 * i) by
          rw [← Nat.pow_add]; congr 1; omega] at *
      simp only [p] at *
      generalize 2 ^ (64 * i) = Bi at *
      generalize 2 ^ (64 * j) = Bj at *
      generalize (mulAddc xi (y.getD j 0) (r.getD (i + j) 0) c).1.toNat = T at *
      generalize (mulAddc xi (y.getD j 0) (r.getD (i + j) 0) c).2.toNat = H at *
      generalize valN (r.set! (i + j) (mulAddc xi (y.getD j 0) (r.getD (i + j) 0) c).1) N = W at *
      generalize (r.getD (i + j) 0).toNat = Rk at *
      generalize xi.toNat = X at *
      generalize (y.getD j 0).toNat = Yj at *
      grind
  | case2 j c r hjm =>
    have hjm' : j = m := by omega
    subst hjm'
    have hs := valN_set! r c (k := i + j) (by omega) N
    rw [if_pos (by omega), if_pos (by omega), hz _ (Nat.le_refl _)] at hs
    refine ⟨by rw [size_set!, hN], fun k hk => ?_, ?_⟩
    · rw [getD_set!, if_neg (by omega), hz k (by omega)]
    · simp only [UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero] at hs
      omega

theorem mulRows_spec (x y : Array UInt64) (n m i : Nat) (r : Array UInt64) (hi : i ≤ n)
    (hN : r.size = n + m) (hz : ∀ k, i + m ≤ k → r.getD k 0 = 0)
    (hv : valN r (n + m) = valN x i * valN y m) :
    (mulRows x y n m i r).size = n + m ∧
      valN (mulRows x y n m i r) (n + m) = valN x n * valN y m := by
  fun_induction mulRows x y n m i r with
  | case1 i r hin xi ih =>
    by_cases h0 : xi = 0
    · rw [if_pos h0]
      rw [dif_pos h0] at ih
      apply ih (by omega) hN (fun k hk => hz k (by omega))
      simp only [valN]
      simp only [xi] at h0
      rw [h0, hv]
      simp
    · rw [if_neg h0]
      rw [dif_neg h0] at ih
      have hr := mulRow_spec xi y m i (n + m) (valN r (n + m)) 0 0 r (Nat.zero_le _) hN
        (by omega) hz (by simp [valN])
      apply ih (by omega) hr.1 (fun k hk => hr.2.1 k (by omega))
      rw [hr.2.2, hv]
      simp only [valN, xi]
      generalize valN x i = A
      generalize valN y m = B
      generalize (x.getD i 0).toNat = X
      grind
  | case2 i r hin =>
    have hin' : i = n := by omega
    subst hin'
    exact ⟨hN, hv⟩

theorem toNatA_of_size_zero (x : Array UInt64) (h : x.size = 0) : toNatA x = 0 := by
  rw [toNatA_eq_valN x (Nat.le_of_eq h)]
  rfl

theorem getD_replicate_zero (N k : Nat) : (Array.replicate N (0 : UInt64)).getD k 0 = 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem valN_replicate_zero (N n : Nat) : valN (Array.replicate N (0 : UInt64)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [valN, ih, getD_replicate_zero]; simp

theorem toNatA_mulA (x y : Array UInt64) : toNatA (mulA x y) = toNatA x * toNatA y := by
  unfold mulA
  split
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [toNatA_of_size_zero x h, Nat.zero_mul]; exact toNatA_of_size_zero #[] rfl
    · rw [toNatA_of_size_zero y h, Nat.mul_zero]; exact toNatA_of_size_zero #[] rfl
  · have h := mulRows_spec x y x.size y.size 0 (Array.replicate (x.size + y.size) 0)
      (Nat.zero_le _) (by simp) (fun k _ => getD_replicate_zero _ k) ?_
    · rw [toNatA_normA, toNatA_eq_valN _ (Nat.le_of_eq h.1), h.2,
        toNatA_eq_valN x (Nat.le_refl _), toNatA_eq_valN y (Nat.le_refl _)]
    · rw [valN, Nat.zero_mul]
      exact valN_replicate_zero _ _

/-! ## Powers -/

/-- `acc * base ^ e` by square-and-multiply over `mulA`. -/
def powA (base : Array UInt64) (e : Nat) (acc : Array UInt64) : Array UInt64 :=
  if e = 0 then acc
  else
    let acc' := if e % 2 = 1 then mulA acc base else acc
    if e / 2 = 0 then acc' else powA (mulA base base) (e / 2) acc'
termination_by e
decreasing_by omega

theorem toNatA_powA (base : Array UInt64) (e : Nat) (acc : Array UInt64) :
    toNatA (powA base e acc) = toNatA acc * toNatA base ^ e := by
  fun_induction powA base e acc with
  | case1 base acc => simp
  | case2 base e acc he acc' h2 =>
    have he' : e = 1 := by omega
    subst he'
    simp [acc', toNatA_mulA]
  | case3 base e acc he acc' h2 ih =>
    rw [ih, toNatA_mulA]
    have hsplit : e = 2 * (e / 2) + e % 2 := by omega
    conv => rhs; rw [hsplit, Nat.pow_add, Nat.pow_mul]
    simp only [acc']
    split
    · rename_i h1
      rw [h1, toNatA_mulA, Nat.pow_one, Nat.pow_two]
      grind
    · rename_i h1
      rw [show e % 2 = 0 by omega, Nat.pow_zero, Nat.pow_two]
      grind

end VerifiedNat
