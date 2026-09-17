/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Limb arithmetic over `Array UInt64` for the lean4lean `Nat` reducer

A natural number is carried as an `Array UInt64` of little-endian base-`2^64`
limbs. The canonical form of `n` (the output of `ofNatA`) has no trailing zero
limbs. This module defines

* the conversions `ofNatA : Nat → Array UInt64` and `toNatA : Array UInt64 → Nat`.
  `toNatA` joins limbs by balanced splitting with `<<<` and `|||`. `ofNatA`
  splits balanced down to blocks of `limbBlock` limbs with `>>>`, `<<<`, `^^^`,
  and reads each limb of a block as `UInt64.ofNat` (the low 64 bits) of a shift
  of the block;
* limb loops for bitwise and, or, xor, left and right shift by a `Nat` bit count,
  and comparison of canonical arrays;
* the value theorems relating each operation to the `Nat` operation, stated
  through the bit characterization `limbBit` of `toNatA`;
* the canonical form `IsCanonA` and `normA_eq_ofNatA`.
-/

namespace VerifiedNat

/-! ## Conversions -/

/-- The value of the `n` limbs of `a` starting at index `lo`, computed by
    splitting the range in half and joining the halves with a shift and an or.
    Missing limbs read as zero. -/
def toNatRange (a : Array UInt64) (lo : Nat) : Nat → Nat
  | 0 => 0
  | 1 => (a.getD lo 0).toNat
  | n + 2 =>
    let h := (n + 2) / 2
    toNatRange a lo h ||| (toNatRange a (lo + h) (n + 2 - h) <<< (64 * h))
termination_by n => n
decreasing_by all_goals omega

/-- The little-endian base-`2 ^ 64` value of a limb array. Decoding `n ≥ 1` limbs
    costs `n` calls of `UInt64.toNat` and `2 * (n - 1)` `Nat` operations (one shift
    and one or per join), which is the least number of binary joins that assemble
    `n` limb values. -/
def toNatA (a : Array UInt64) : Nat := toNatRange a 0 a.size

/-- The largest number of limbs `pushLimbs` extracts from one `Nat` by `pushBlock`. -/
def limbBlock : Nat := 16

/-- Push the `k` low limbs of `blk`, least significant first, onto `acc`. Limb `0`
    is `UInt64.ofNat blk` (the low 64 bits) and the remaining limbs are those of
    `blk >>> 64`. Extracting `k ≥ 1` limbs costs `k` calls of `UInt64.ofNat` and
    `k - 1` shifts. -/
def pushBlock (blk : Nat) : Nat → Array UInt64 → Array UInt64
  | 0, acc => acc
  | 1, acc => acc.push (UInt64.ofNat blk)
  | k + 2, acc => pushBlock (blk >>> 64) (k + 1) (acc.push (UInt64.ofNat blk))

/-- The split point of a `k`-limb range in `pushLimbs`: half of the
    `⌈k / limbBlock⌉` blocks, rounded down, measured in limbs. -/
def splitLimbs (k : Nat) : Nat := limbBlock * ((k + limbBlock - 1) / limbBlock / 2)

theorem splitLimbs_bounds {k : Nat} (hk : ¬ k ≤ limbBlock) :
    0 < splitLimbs k ∧ splitLimbs k < k := by
  simp only [splitLimbs, limbBlock] at *; omega

/-- Push the `k` low limbs of `n`, least significant first, onto `acc`. A range
    of at most `limbBlock` limbs is extracted by `pushBlock`. A longer range splits
    at `h = splitLimbs k` limbs: the low part is `n ^^^ ((n >>> m) <<< m)` and the
    high part is `n >>> m`, with `m = 64 * h`, so every low part is a whole number
    of blocks.

    With `q = ⌈k / limbBlock⌉` blocks, the extraction of `k ≥ 1` limbs costs
    `3 * (q - 1)` `Nat` operations for the splits, `k - q` shifts inside the
    blocks and `k` calls of `UInt64.ofNat`: `2 * k + 2 * q - 3` runtime calls. -/
def pushLimbs (n k : Nat) (acc : Array UInt64) : Array UInt64 :=
  if _hk : k ≤ limbBlock then pushBlock n k acc
  else
    let h := splitLimbs k
    let hi := n >>> (64 * h)
    let lo := n ^^^ (hi <<< (64 * h))
    pushLimbs hi (k - h) (pushLimbs lo h acc)
termination_by k
decreasing_by all_goals have := splitLimbs_bounds _hk; omega

/-- The number of limbs of the canonical form of `n`. -/
def limbCount (n : Nat) : Nat := if n = 0 then 0 else n.log2 / 64 + 1

/-- The canonical little-endian limb array of `n`. -/
def ofNatA (n : Nat) : Array UInt64 :=
  pushLimbs n (limbCount n) (Array.emptyWithCapacity (limbCount n))

/-- Remove trailing zero limbs. -/
def normA (x : Array UInt64) : Array UInt64 :=
  if h : x.size = 0 then x
  else if x[x.size - 1] = 0 then normA x.pop else x
termination_by x.size
decreasing_by simp only [Array.size_pop]; omega

/-! ## Limb loops -/

/-- Limb-wise and, the shorter operand padded with zero limbs, normalized. -/
def landA (x y : Array UInt64) : Array UInt64 :=
  normA (Array.ofFn (n := min x.size y.size) fun i => x.getD i 0 &&& y.getD i 0)

/-- Limb-wise or, the shorter operand padded with zero limbs. -/
def lorA (x y : Array UInt64) : Array UInt64 :=
  Array.ofFn (n := max x.size y.size) fun i => x.getD i 0 ||| y.getD i 0

/-- Limb-wise xor, the shorter operand padded with zero limbs, normalized. -/
def xorA (x y : Array UInt64) : Array UInt64 :=
  normA (Array.ofFn (n := max x.size y.size) fun i => x.getD i 0 ^^^ y.getD i 0)

/-- Output limb `i` of a left shift by `r` bits (`r < 64`) of the limbs of `x`:
    limb `i` shifted left, or'ed with the bits carried out of limb `i - 1`. -/
@[inline] def shlLimb (x : Array UInt64) (r : Nat) (i : Nat) : UInt64 :=
  if r = 0 then x.getD i 0
  else
    (x.getD i 0 <<< UInt64.ofNat r) |||
      (if i = 0 then 0 else x.getD (i - 1) 0 >>> UInt64.ofNat (64 - r))

/-- Left shift by `s` bits: `s / 64` zero limbs followed by the limbs shifted
    by `s % 64` bits with carry, normalized. -/
def shiftLeftA (x : Array UInt64) (s : Nat) : Array UInt64 :=
  if x.size = 0 then #[]
  else
    let q := s / 64
    let r := s % 64
    normA (Array.ofFn (n := q + x.size + 1) fun k =>
      if k.val < q then 0 else shlLimb x r (k.val - q))

/-- Output limb `i` of a right shift by `r` bits (`r < 64`) of the limbs of `x`
    from index `q` on: limb `q + i` shifted right, or'ed with the low bits of
    limb `q + i + 1`. -/
@[inline] def shrLimb (x : Array UInt64) (q r : Nat) (i : Nat) : UInt64 :=
  if r = 0 then x.getD (q + i) 0
  else
    (x.getD (q + i) 0 >>> UInt64.ofNat r) |||
      (x.getD (q + i + 1) 0 <<< UInt64.ofNat (64 - r))

/-- Right shift by `s` bits: drop `s / 64` limbs, shift the rest right by
    `s % 64` bits with carry, normalized. -/
def shiftRightA (x : Array UInt64) (s : Nat) : Array UInt64 :=
  let q := s / 64
  if x.size ≤ q then #[]
  else
    let r := s % 64
    normA (Array.ofFn (n := x.size - q) fun i => shrLimb x q r i.val)

/-- Compare the limbs below index `i`, from the most significant down. -/
def cmpLimbs (x y : Array UInt64) : Nat → Ordering
  | 0 => .eq
  | i + 1 =>
    let a := x.getD i 0
    let b := y.getD i 0
    if a < b then .lt else if b < a then .gt else cmpLimbs x y i

/-- Comparison of canonical limb arrays: by size, then limb-wise from the most
    significant limb. -/
def cmpA (x y : Array UInt64) : Ordering :=
  if x.size < y.size then .lt
  else if y.size < x.size then .gt
  else cmpLimbs x y x.size

/-- Equality of canonical limb arrays. -/
def beqA (x y : Array UInt64) : Bool := x == y

/-- `≤` on canonical limb arrays. -/
def bleA (x y : Array UInt64) : Bool := cmpA x y != .gt

/-! ## Bit characterization -/

/-- Bit `j` of the value of a limb array: bit `j % 64` of limb `j / 64`, with
    missing limbs reading as zero. -/
def limbBit (a : Array UInt64) (j : Nat) : Bool := (a.getD (j / 64) 0).toNat.testBit (j % 64)

theorem testBit_toNat_of_ge (v : UInt64) {j : Nat} (h : 64 ≤ j) : v.toNat.testBit j = false := by
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le v.toNat_lt (Nat.pow_le_pow_right (by decide) h))

theorem testBit_toNatRange (a : Array UInt64) (lo n j : Nat) :
    (toNatRange a lo n).testBit j =
      (decide (j < 64 * n) && (a.getD (lo + j / 64) 0).toNat.testBit (j % 64)) := by
  induction n using Nat.strongRecOn generalizing lo j with
  | _ n ih =>
    match n with
    | 0 => simp [toNatRange]
    | 1 =>
      rw [toNatRange]
      by_cases hj : j < 64
      · have h1 : j / 64 = 0 := by omega
        have h2 : j % 64 = j := by omega
        simp [hj, h1, h2]
      · simp [hj, testBit_toNat_of_ge _ (show 64 ≤ j by omega)]
    | n + 2 =>
      rw [toNatRange]
      simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
      rw [ih _ (by omega), ih _ (by omega)]
      have hb1 : (n + 2) / 2 ≤ n + 2 := Nat.div_le_self _ _
      generalize (n + 2) / 2 = h at hb1 ⊢
      by_cases hj : j < 64 * h
      · rw [decide_eq_true hj, decide_eq_true (show j < 64 * (n + 2) by omega),
          decide_eq_false (show ¬ j ≥ 64 * h by omega)]
        simp
      · have e1 : lo + h + (j - 64 * h) / 64 = lo + j / 64 := by omega
        have e2 : (j - 64 * h) % 64 = j % 64 := by omega
        have e3 : (j - 64 * h < 64 * (n + 2 - h)) = (j < 64 * (n + 2)) := by
          apply propext; omega
        rw [decide_eq_false hj, decide_eq_true (show j ≥ 64 * h by omega), e1, e2]
        simp only [e3]
        simp

theorem testBit_toNatA (a : Array UInt64) (j : Nat) : (toNatA a).testBit j = limbBit a j := by
  rw [toNatA, testBit_toNatRange, limbBit, Nat.zero_add]
  by_cases hj : j < 64 * a.size
  · simp [hj]
  · have : a.getD (j / 64) 0 = 0 := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (show a.size ≤ j / 64 by omega)]
    simp [hj, this]

theorem getD_zero_of_size_le (a : Array UInt64) {i : Nat} (h : a.size ≤ i) : a.getD i 0 = 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

theorem pushBlock_size (n k : Nat) (acc : Array UInt64) :
    (pushBlock n k acc).size = acc.size + k := by
  induction k using Nat.strongRecOn generalizing n acc with
  | _ k ih =>
    match k with
    | 0 => simp [pushBlock]
    | 1 => simp [pushBlock]
    | k + 2 =>
      rw [pushBlock, ih _ (by omega)]
      simp only [Array.size_push]
      omega

theorem pushBlock_bit (n k : Nat) (acc : Array UInt64) (i b : Nat) (hb : b < 64) :
    ((pushBlock n k acc).getD i 0).toNat.testBit b =
      if i < acc.size then (acc.getD i 0).toNat.testBit b
      else (decide (i < acc.size + k) && n.testBit (64 * (i - acc.size) + b)) := by
  induction k using Nat.strongRecOn generalizing n acc with
  | _ k ih =>
    match k with
    | 0 =>
      rw [pushBlock]
      by_cases hi : i < acc.size
      · simp [hi]
      · simp [hi, getD_zero_of_size_le acc (Nat.le_of_not_lt hi)]
    | 1 =>
      rw [pushBlock]
      by_cases hi : i < acc.size
      · simp [hi, Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hi]
      · by_cases he : i = acc.size
        · subst he
          simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos, Option.getD_some,
            UInt64.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.lt_irrefl, if_false, hb,
            decide_true, Bool.true_and, Nat.sub_self, Nat.mul_zero, Nat.zero_add,
            Nat.lt_add_one]
        · rw [getD_zero_of_size_le _ (by simp; omega)]
          simp [hi, show ¬ i < acc.size + 1 by omega]
    | k + 2 =>
      have e : acc.push (UInt64.ofNat n) = pushBlock n 1 acc := rfl
      rw [pushBlock, e, ih _ (by omega), pushBlock_size, ih _ (by omega)]
      by_cases hi : i < acc.size + 1
      · rw [if_pos hi]
        by_cases hi' : i < acc.size
        · simp [hi']
        · rw [if_neg hi', if_neg hi', decide_eq_true hi,
            decide_eq_true (by omega : i < acc.size + (k + 2))]
      · rw [if_neg hi, if_neg (by omega : ¬ i < acc.size), Nat.testBit_shiftRight]
        have e1 : 64 + (64 * (i - (acc.size + 1)) + b) = 64 * (i - acc.size) + b := by omega
        have e2 : (i < acc.size + 1 + (k + 1)) = (i < acc.size + (k + 2)) := by
          apply propext; omega
        rw [e1]
        simp only [e2]

theorem pushLimbs_size (n k : Nat) (acc : Array UInt64) :
    (pushLimbs n k acc).size = acc.size + k := by
  induction k using Nat.strongRecOn generalizing n acc with
  | _ k ih =>
    rw [pushLimbs]
    split
    · exact pushBlock_size _ _ _
    · rename_i hk
      have hb := splitLimbs_bounds hk
      dsimp only
      rw [ih _ (by omega), ih _ (by omega)]
      omega

theorem pushLimbs_bit (n k : Nat) (acc : Array UInt64) (i b : Nat) (hb : b < 64) :
    ((pushLimbs n k acc).getD i 0).toNat.testBit b =
      if i < acc.size then (acc.getD i 0).toNat.testBit b
      else (decide (i < acc.size + k) && n.testBit (64 * (i - acc.size) + b)) := by
  induction k using Nat.strongRecOn generalizing n acc with
  | _ k ih =>
    rw [pushLimbs]
    split
    · exact pushBlock_bit _ _ _ _ _ hb
    · rename_i hk
      have hb1 := splitLimbs_bounds hk
      dsimp only
      rw [ih _ (by omega), pushLimbs_size]
      generalize splitLimbs k = h at hb1 ⊢
      by_cases hi : i < acc.size + h
      · rw [if_pos hi, ih _ (by omega)]
        by_cases hi' : i < acc.size
        · simp [hi']
        · rw [if_neg hi', if_neg hi', decide_eq_true hi, decide_eq_true (by omega : i < acc.size + k)]
          simp only [Bool.true_and, Nat.testBit_xor, Nat.testBit_shiftLeft]
          rw [decide_eq_false (by omega : ¬ 64 * (i - acc.size) + b ≥ 64 * h)]
          simp
      · rw [if_neg hi, if_neg (by omega : ¬ i < acc.size), Nat.testBit_shiftRight]
        have e1 : 64 * h + (64 * (i - (acc.size + h)) + b) = 64 * (i - acc.size) + b := by omega
        have e2 : (i < acc.size + h + (k - h)) = (i < acc.size + k) := by
          apply propext; omega
        rw [e1]
        simp only [e2]

theorem size_ofNatA (n : Nat) : (ofNatA n).size = limbCount n := by
  simp [ofNatA, pushLimbs_size]

theorem limbBit_ofNatA (n j : Nat) : limbBit (ofNatA n) j = n.testBit j := by
  unfold limbBit ofNatA
  rw [pushLimbs_bit _ _ _ _ _ (Nat.mod_lt _ (by decide))]
  simp only [Array.emptyWithCapacity_eq, List.size_toArray, List.length_nil, Nat.not_lt_zero, if_false, Nat.sub_zero, Nat.zero_add]
  rw [show 64 * (j / 64) + j % 64 = j by omega]
  by_cases hj : j / 64 < limbCount n
  · simp [hj]
  · rw [decide_eq_false hj, Bool.false_and]
    unfold limbCount at hj
    split at hj
    · subst n; simp
    · exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
        (Nat.pow_le_pow_right (by decide) (by omega)))).symm

/-- The canonical limb array decodes to the number it encodes. -/
theorem toNatA_ofNatA (n : Nat) : toNatA (ofNatA n) = n :=
  Nat.eq_of_testBit_eq fun j => by rw [testBit_toNatA, limbBit_ofNatA]

theorem getD_normA (x : Array UInt64) (i : Nat) : (normA x).getD i 0 = x.getD i 0 := by
  fun_induction normA x with
  | case1 => rfl
  | case2 x h h0 ih =>
    rw [ih]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_pop]
    split
    · rfl
    · by_cases hi : i = x.size - 1
      · subst hi
        rw [Array.getElem?_eq_getElem (by omega)]
        simp [h0]
      · rw [Array.getElem?_eq_none (by omega)]
  | case3 => rfl

theorem limbBit_normA (x : Array UInt64) (j : Nat) : limbBit (normA x) j = limbBit x j := by
  simp only [limbBit, getD_normA]

theorem getD_ofFn {m : Nat} (f : Fin m → UInt64) (i : Nat) :
    (Array.ofFn f).getD i 0 = if h : i < m then f ⟨i, h⟩ else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split <;> rfl

theorem limbBit_landA (x y : Array UInt64) (j : Nat) :
    limbBit (landA x y) j = (limbBit x j && limbBit y j) := by
  simp only [landA, limbBit, getD_normA, getD_ofFn]
  split
  · simp only [UInt64.toNat_and, Nat.testBit_and]
  · rcases Nat.le_total x.size y.size with h | h
    · rw [getD_zero_of_size_le x (i := j / 64) (by omega)]; simp
    · rw [getD_zero_of_size_le y (i := j / 64) (by omega)]; simp

theorem limbBit_lorA (x y : Array UInt64) (j : Nat) :
    limbBit (lorA x y) j = (limbBit x j || limbBit y j) := by
  simp only [lorA, limbBit, getD_ofFn]
  split
  · simp only [UInt64.toNat_or, Nat.testBit_or]
  · rw [getD_zero_of_size_le x (i := j / 64) (by omega),
      getD_zero_of_size_le y (i := j / 64) (by omega)]
    simp

theorem limbBit_xorA (x y : Array UInt64) (j : Nat) :
    limbBit (xorA x y) j = (limbBit x j ^^ limbBit y j) := by
  simp only [xorA, limbBit, getD_normA, getD_ofFn]
  split
  · simp only [UInt64.toNat_xor, Nat.testBit_xor]
  · rw [getD_zero_of_size_le x (i := j / 64) (by omega),
      getD_zero_of_size_le y (i := j / 64) (by omega)]
    simp

theorem toNatA_landA (x y : Array UInt64) : toNatA (landA x y) = toNatA x &&& toNatA y :=
  Nat.eq_of_testBit_eq fun j => by simp only [testBit_toNatA, Nat.testBit_and, limbBit_landA]

theorem toNatA_lorA (x y : Array UInt64) : toNatA (lorA x y) = toNatA x ||| toNatA y :=
  Nat.eq_of_testBit_eq fun j => by simp only [testBit_toNatA, Nat.testBit_or, limbBit_lorA]

theorem toNatA_xorA (x y : Array UInt64) : toNatA (xorA x y) = toNatA x ^^^ toNatA y :=
  Nat.eq_of_testBit_eq fun j => by simp only [testBit_toNatA, Nat.testBit_xor, limbBit_xorA]

theorem limbBit_eq (x : Array UInt64) {m i u : Nat} (h : m = 64 * i + u) (hu : u < 64) :
    limbBit x m = (x.getD i 0).toNat.testBit u := by
  subst h
  simp only [limbBit]
  rw [show (64 * i + u) / 64 = i by omega, show (64 * i + u) % 64 = u by omega]

theorem limbBit_of_size_le (x : Array UInt64) {m : Nat} (h : 64 * x.size ≤ m) :
    limbBit x m = false := by
  simp only [limbBit]
  rw [getD_zero_of_size_le x (by omega)]
  simp

theorem toNat_ofNat_of_lt {r : Nat} (hr : r < 64) : (UInt64.ofNat r).toNat % 64 = r := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega), Nat.mod_eq_of_lt hr]

theorem testBit_shl64 (v : UInt64) {r t : Nat} (hr : r < 64) (ht : t < 64) :
    (v <<< UInt64.ofNat r).toNat.testBit t = (decide (r ≤ t) && v.toNat.testBit (t - r)) := by
  rw [UInt64.toNat_shiftLeft, toNat_ofNat_of_lt hr, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, decide_eq_true ht]
  simp only [Bool.true_and, ge_iff_le]

theorem testBit_shr64 (v : UInt64) {r : Nat} (hr : r < 64) (t : Nat) :
    (v >>> UInt64.ofNat r).toNat.testBit t = v.toNat.testBit (r + t) := by
  rw [UInt64.toNat_shiftRight, toNat_ofNat_of_lt hr, Nat.testBit_shiftRight]

theorem limbBit_shiftLeftA (x : Array UInt64) (s j : Nat) :
    limbBit (shiftLeftA x s) j = (decide (s ≤ j) && limbBit x (j - s)) := by
  unfold shiftLeftA
  split
  · rename_i h0
    rw [limbBit_of_size_le x (by omega), limbBit_of_size_le #[] (by simp)]
    simp
  · simp only [limbBit, getD_normA, getD_ofFn]
    have ht : j % 64 < 64 := Nat.mod_lt _ (by decide)
    have hr : s % 64 < 64 := Nat.mod_lt _ (by decide)
    split
    · rename_i hK
      split
      · rename_i hq
        rw [decide_eq_false (show ¬ s ≤ j by omega)]
        simp
      · rename_i hq
        unfold shlLimb
        split
        · rename_i hr0
          rw [decide_eq_true (show s ≤ j by omega)]
          rw [← limbBit, limbBit_eq x (i := j / 64 - s / 64) (u := j % 64) (by omega) ht]
          simp
        · rename_i hr0
          rw [UInt64.toNat_or, Nat.testBit_or, testBit_shl64 _ hr ht]
          by_cases htr : s % 64 ≤ j % 64
          · rw [decide_eq_true htr, decide_eq_true (show s ≤ j by omega), Bool.true_and,
              Bool.true_and, ← limbBit,
              limbBit_eq x (i := j / 64 - s / 64) (u := j % 64 - s % 64) (by omega) (by omega)]
            split
            · simp
            · rw [testBit_shr64 _ (by omega),
                testBit_toNat_of_ge _ (j := 64 - s % 64 + j % 64) (by omega)]
              simp
          · rw [decide_eq_false htr, Bool.false_and, Bool.false_or]
            split
            · rename_i hi0
              rw [decide_eq_false (show ¬ s ≤ j by omega)]
              simp
            · rename_i hi0
              rw [testBit_shr64 _ (by omega), decide_eq_true (show s ≤ j by omega), Bool.true_and,
                ← limbBit, limbBit_eq x (i := j / 64 - s / 64 - 1)
                  (u := 64 - s % 64 + j % 64) (by omega) (by omega)]
    · rename_i hK
      rw [← limbBit, limbBit_of_size_le x (m := j - s) (by omega)]
      simp

theorem limbBit_shiftRightA (x : Array UInt64) (s j : Nat) :
    limbBit (shiftRightA x s) j = limbBit x (j + s) := by
  unfold shiftRightA
  dsimp only
  split
  · rename_i h0
    rw [limbBit_of_size_le x (by omega), limbBit_of_size_le #[] (by simp)]
  · simp only [limbBit, getD_normA, getD_ofFn]
    have ht : j % 64 < 64 := Nat.mod_lt _ (by decide)
    have hr : s % 64 < 64 := Nat.mod_lt _ (by decide)
    split
    · rename_i hK
      rw [← limbBit]
      unfold shrLimb
      split
      · rename_i hr0
        rw [limbBit_eq x (i := s / 64 + j / 64) (u := j % 64) (by omega) ht]
      · rename_i hr0
        rw [UInt64.toNat_or, Nat.testBit_or, testBit_shr64 _ hr,
          testBit_shl64 _ (by omega) ht]
        by_cases hc : s % 64 + j % 64 < 64
        · rw [decide_eq_false (show ¬ 64 - s % 64 ≤ j % 64 by omega), Bool.false_and,
            Bool.or_false, limbBit_eq x (i := s / 64 + j / 64) (u := s % 64 + j % 64)
              (by omega) hc]
        · rw [testBit_toNat_of_ge _ (by omega), Bool.false_or,
            decide_eq_true (show 64 - s % 64 ≤ j % 64 by omega), Bool.true_and,
            limbBit_eq x (i := s / 64 + j / 64 + 1) (u := j % 64 - (64 - s % 64))
              (by omega) (by omega)]
    · rename_i hK
      rw [← limbBit, limbBit_of_size_le x (by omega)]
      simp

theorem toNatA_shiftLeftA (x : Array UInt64) (s : Nat) :
    toNatA (shiftLeftA x s) = toNatA x <<< s :=
  Nat.eq_of_testBit_eq fun j => by
    simp only [testBit_toNatA, Nat.testBit_shiftLeft, limbBit_shiftLeftA, ge_iff_le]

theorem toNatA_shiftRightA (x : Array UInt64) (s : Nat) :
    toNatA (shiftRightA x s) = toNatA x >>> s :=
  Nat.eq_of_testBit_eq fun j => by
    simp only [testBit_toNatA, Nat.testBit_shiftRight, limbBit_shiftRightA, Nat.add_comm]

/-! ## Comparison -/

theorem toNatA_lt (x : Array UInt64) : toNatA x < 2 ^ (64 * x.size) :=
  Nat.lt_pow_two_of_testBit _ fun j hj => by
    rw [testBit_toNatA, limbBit_of_size_le x hj]

theorem pow_le_of_limbCount (n : Nat) (h : 0 < limbCount n) :
    2 ^ (64 * (limbCount n - 1)) ≤ n := by
  by_cases hn : n = 0
  · simp [limbCount, hn] at h
  · simp only [limbCount, hn, if_false, Nat.add_sub_cancel]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.log2_self_le hn)

theorem shiftRight_limb (x : Array UInt64) (i : Nat) :
    toNatA x >>> (64 * i) = (toNatA x >>> (64 * (i + 1))) * 2 ^ 64 + (x.getD i 0).toNat := by
  rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt _)]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, testBit_toNatA]
  by_cases hj : 64 ≤ j
  · rw [testBit_toNat_of_ge _ hj, decide_eq_true hj, Bool.true_and, Bool.or_false,
      show 64 * (i + 1) + (j - 64) = 64 * i + j by omega]
  · rw [decide_eq_false hj, Bool.false_and, Bool.false_or,
      limbBit_eq x (i := i) (u := j) rfl (by omega)]

theorem lt_of_shiftRight_lt {a b k : Nat} (h : a >>> k < b >>> k) : a < b := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at h
  exact Nat.lt_of_not_le fun hle => Nat.not_le_of_lt h (Nat.div_le_div_right hle)

theorem cmpLimbs_eq (x y : Array UInt64) (i : Nat)
    (h : toNatA x >>> (64 * i) = toNatA y >>> (64 * i)) :
    cmpLimbs x y i = compare (toNatA x) (toNatA y) := by
  induction i with
  | zero =>
    simp only [Nat.mul_zero, Nat.shiftRight_zero] at h
    rw [cmpLimbs, h]
    exact (Nat.compare_eq_eq.mpr rfl).symm
  | succ i ih =>
    rw [cmpLimbs]
    split
    · rename_i hab
      rw [UInt64.lt_iff_toNat_lt] at hab
      refine (Nat.compare_eq_lt.mpr (lt_of_shiftRight_lt (k := 64 * i) ?_)).symm
      rw [shiftRight_limb x i, shiftRight_limb y i, h]
      omega
    · split
      · rename_i _ hba
        rw [UInt64.lt_iff_toNat_lt] at hba
        refine (Nat.compare_eq_gt.mpr (lt_of_shiftRight_lt (k := 64 * i) ?_)).symm
        rw [shiftRight_limb x i, shiftRight_limb y i, h]
        omega
      · rename_i hab hba
        rw [UInt64.lt_iff_toNat_lt] at hab hba
        apply ih
        rw [shiftRight_limb x i, shiftRight_limb y i, h]
        omega

/-- Comparison of canonical limb arrays agrees with `compare` on `Nat`. -/
theorem cmpA_ofNatA (a b : Nat) : cmpA (ofNatA a) (ofNatA b) = compare a b := by
  have ha := toNatA_lt (ofNatA a)
  have hb := toNatA_lt (ofNatA b)
  rw [toNatA_ofNatA, size_ofNatA] at ha
  rw [toNatA_ofNatA, size_ofNatA] at hb
  unfold cmpA
  rw [size_ofNatA, size_ofNatA]
  split
  · rename_i hlt
    refine (Nat.compare_eq_lt.mpr ?_).symm
    exact Nat.lt_of_lt_of_le ha (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega))
      (pow_le_of_limbCount b (by omega)))
  · split
    · rename_i _ hlt
      refine (Nat.compare_eq_gt.mpr ?_).symm
      exact Nat.lt_of_lt_of_le hb (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega))
        (pow_le_of_limbCount a (by omega)))
    · rename_i h1 h2
      have hk : limbCount a = limbCount b := by omega
      rw [cmpLimbs_eq _ _ _ ?_, toNatA_ofNatA, toNatA_ofNatA]
      rw [toNatA_ofNatA, toNatA_ofNatA, Nat.shiftRight_eq_zero _ _ ha,
        hk, Nat.shiftRight_eq_zero _ _ hb]

/-- Equality of canonical limb arrays agrees with `Nat.beq`. -/
theorem beqA_ofNatA (a b : Nat) : beqA (ofNatA a) (ofNatA b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beqA, beq_iff_eq]
  constructor
  · intro h
    rw [← toNatA_ofNatA a, h, toNatA_ofNatA]
  · intro h
    rw [h]

/-- `≤` on canonical limb arrays agrees with `Nat.ble`. -/
theorem bleA_ofNatA (a b : Nat) : bleA (ofNatA a) (ofNatA b) = Nat.ble a b := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, bleA, cmpA_ofNatA, bne_iff_ne, ne_eq]
  rw [Nat.compare_eq_gt]
  omega

/-! ## Canonical form -/

/-- A limb array is canonical when it is empty or its last limb is nonzero. -/
def IsCanonA (a : Array UInt64) : Prop := ∀ h : 0 < a.size, a[a.size - 1] ≠ 0

theorem isCanonA_normA (x : Array UInt64) : IsCanonA (normA x) := by
  fun_induction normA x with
  | case1 x h => intro h'; omega
  | case2 x h h0 ih => exact ih
  | case3 x h h0 => intro _; exact h0

theorem size_eq_limbCount_of_isCanonA {a : Array UInt64} (h : IsCanonA a) :
    a.size = limbCount (toNatA a) := by
  have hlt := toNatA_lt a
  by_cases hs : a.size = 0
  · rw [hs, Nat.mul_zero, Nat.pow_zero, Nat.lt_one_iff] at hlt
    simp [limbCount, hlt, hs]
  · obtain ⟨t, ht⟩ := Nat.exists_testBit_of_ne_zero (x := (a[a.size - 1]'(by omega)).toNat)
      (fun h0 => h (by omega) (UInt64.toNat_inj.mp (by rw [h0]; rfl)))
    have ht64 : t < 64 := by
      apply Nat.lt_of_not_le
      intro hle
      rw [testBit_toNat_of_ge _ hle] at ht
      cases ht
    have hbit : (toNatA a).testBit (64 * (a.size - 1) + t) = true := by
      rw [testBit_toNatA, limbBit_eq a rfl ht64,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
      exact ht
    have hge := Nat.ge_two_pow_of_testBit hbit
    have hne : toNatA a ≠ 0 := fun h0 => by
      rw [h0] at hge; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hge)
    have h1 := (Nat.log2_lt hne).2 hlt
    have h2 := (Nat.le_log2 hne).2
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ t)) hge)
    simp only [limbCount, hne, if_false]
    omega

/-- A canonical limb array is the `ofNatA` encoding of its value. -/
theorem eq_ofNatA_of_isCanonA {a : Array UInt64} (h : IsCanonA a) :
    a = ofNatA (toNatA a) := by
  have hs : a.size = (ofNatA (toNatA a)).size := by
    rw [size_ofNatA, size_eq_limbCount_of_isCanonA h]
  refine Array.ext hs fun i h1 h2 => UInt64.toNat_inj.mp (Nat.eq_of_testBit_eq fun u => ?_)
  by_cases hu : u < 64
  · have e1 := limbBit_eq a (i := i) rfl hu
    have e2 := limbBit_eq (ofNatA (toNatA a)) (i := i) rfl hu
    rw [limbBit_ofNatA] at e2
    have g1 : a[i] = a.getD i 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some]
    have g2 : (ofNatA (toNatA a))[i] = (ofNatA (toNatA a)).getD i 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2, Option.getD_some]
    rw [g1, g2, ← e1, ← e2, testBit_toNatA]
  · rw [testBit_toNat_of_ge _ (by omega), testBit_toNat_of_ge _ (by omega)]

/-- Normalizing a limb array yields the `ofNatA` encoding of its value. -/
theorem normA_eq_ofNatA (x : Array UInt64) : normA x = ofNatA (toNatA x) := by
  have hv : toNatA (normA x) = toNatA x :=
    Nat.eq_of_testBit_eq fun j => by rw [testBit_toNatA, testBit_toNatA, limbBit_normA]
  rw [← hv]
  exact eq_ofNatA_of_isCanonA (isCanonA_normA x)

theorem isCanonA_ofNatA (n : Nat) : IsCanonA (ofNatA n) := by
  have h := normA_eq_ofNatA (ofNatA n)
  rw [toNatA_ofNatA] at h
  exact h ▸ isCanonA_normA _

end VerifiedNat
