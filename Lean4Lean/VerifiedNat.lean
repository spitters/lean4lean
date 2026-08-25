/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Verified limb-kernel arithmetic for the lean4lean `Nat` reducer

lean4lean's kernel reduces closed `Nat` literal operations by applying the plain
Lean `Nat` operations (`Nat.add`, `Nat.mul`, …), which are `@[extern lean_nat_*]`
and therefore run GMP at runtime. This module supplies drop-in replacements whose
LOGICAL body is the same `Nat` operation (so they are equal to it by `rfl`) and
whose COMPILED body (`@[implemented_by]`) decodes each operand to a little-endian
base-`2^64` limb list, runs a verified limb kernel, and re-encodes.

The limb kernels are vendored verbatim from the CatCrypt SSProve development
(`CatCrypt/Crypto/SecureCompilation/{MultiLimbKernel,BigNat,BigNatKaratsuba,
BigNatShift,BigNatBitwise}.lean`), where each carries a machine-checked value
specification against `bignumVal` (the abstraction function `toNat`):

* `bnAdd_val`      : `bignumVal (bnAdd xs ys c) = bignumVal xs + bignumVal ys + c.toNat`
* `mulBignum_val`  : `bignumVal (mulBignum as bs) = bignumVal as * bignumVal bs`
* `karatsuba_val`  : `bignumVal (karatsuba a b) = bignumVal a * bignumVal b`
* `bnSub_val`      : `bignumVal (bnSub a b) = bignumVal a - bignumVal b`
* `shl_shiftLeft`  : `bignumVal (shl a y) = bignumVal a <<< y`
* `shr_shiftRight` : `bignumVal (shr a y) = bignumVal a >>> y`
* `land_val`/`lor_val`/`xor_val` : the bitwise value specs
* `toNat_ofNat`    : `bignumVal (ofNat n) = n`

`pow` (square-and-multiply over the Karatsuba multiply), `beq` and `ble` (via the
verified subtraction) are composed from those kernels here. `div` and `mod` use
the single-limb long-division kernel `divmodLE` (a `128 / 64 → 64` window per
limb) for a divisor below `2 ^ 64`, and fall back to the stock `Nat` operation
for a multi-limb divisor (limb-native Knuth-D division is not vendored here).
`gcd` is the Euclidean algorithm over the routed `mod`.

Coverage: add, sub, mul (Karatsuba dispatch), pow, shiftLeft, shiftRight, land,
lor, xor, beq, ble, gcd, and div/mod (single-limb divisor) route through verified
limbs; div/mod with a multi-limb divisor fall back to the stock `Nat` path.
-/

namespace VerifiedNat

/-! ## Vendored verified limb kernels (pure core Lean: `List` + `BitVec`) -/

/-- Branchless unsigned less-than as a 0/1 word (borrow-out of `a - b`). -/
def bSltu (a b : BitVec 64) : BitVec 64 :=
  ((~~~a &&& b) ||| (~~~(a ^^^ b) &&& (a - b))) >>> 63

/-- Balanced product-tree evaluation of a little-endian limb list: split the
    list in half, evaluate each half, and combine as
    `bignumVal lo + 2 ^ (64 * lo.length) * bignumVal hi`. One big-`Nat` shift per
    recursion level and `O(log n)` levels, versus the `O(n^2)` linear Horner chain. -/
def bignumValFast : List (BitVec 64) → Nat
  | [] => 0
  | [x] => x.toNat
  | (x :: y :: rest) =>
    let l := x :: y :: rest
    let h := l.length / 2
    bignumValFast (l.take h) + 2 ^ (64 * h) * bignumValFast (l.drop h)
termination_by l => l.length
decreasing_by
  · simp only [List.length_take, List.length_cons]; omega
  · simp only [List.length_drop, List.length_cons]; omega

/-- Little-endian limb-list value (abstraction function `toNat`). The logical
    body is the linear Horner chain; the compiled body is `bignumValFast`, which
    computes the same `Nat` by balanced recombination. -/
@[implemented_by bignumValFast]
def bignumVal : List (BitVec 64) → Nat
  | [] => 0
  | l :: ls => l.toNat + 2 ^ 64 * bignumVal ls

/-- High limb of the 128-bit wide product `a * b`. -/
def mulhi (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)

/-- Scalar × bignum with running carry: `mulScalar a bs c` represents `a * val bs + c`. -/
def mulScalar (a : BitVec 64) : List (BitVec 64) → BitVec 64 → List (BitVec 64)
  | [], c => [c]
  | b :: bs, c => (a * b + c) :: mulScalar a bs (mulhi a b + bSltu (a * b + c) (a * b))

/-- Uneven-length bignum add with carry. -/
def bnAdd : List (BitVec 64) → List (BitVec 64) → BitVec 64 → List (BitVec 64)
  | [], [], c => [c]
  | [], y :: ys, c => (y + c) :: bnAdd [] ys (bSltu (y + c) y)
  | x :: xs, [], c => (x + c) :: bnAdd xs [] (bSltu (x + c) x)
  | x :: xs, y :: ys, c =>
      (x + y + c) :: bnAdd xs ys (bSltu (x + y) x + bSltu (x + y + c) (x + y))

/-- Full schoolbook N-limb multiplication (accumulate shifted scalar products). -/
def mulBignum : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], _ => []
  | a :: as, bs => bnAdd (mulScalar a bs 0) (0 :: mulBignum as bs) 0

/-- Equal-length schoolbook add with carry (final carry becomes the top limb). -/
def addLimbs : List (BitVec 64) → List (BitVec 64) → BitVec 64 → List (BitVec 64)
  | a :: as, b :: bs, c =>
      (a + b + c) :: addLimbs as bs (bSltu (a + b) a + bSltu (a + b + c) (a + b))
  | _, _, c => [c]

/-- Bitwise-complement every limb (the `~y` of two's-complement subtract). -/
def notLimbs (ys : List (BitVec 64)) : List (BitVec 64) := ys.map (~~~·)

/-- Multi-limb subtract `x − y` as two's complement: complement `y`, add with
    carry `1`. Produces `x.length + 1` limbs; the top limb is the not-borrow flag. -/
def subLimbs (xs ys : List (BitVec 64)) : List (BitVec 64) :=
  addLimbs xs (notLimbs ys) 1

/-- Branchless per-limb select: mask all-ones picks `a`, mask zero picks `b`. -/
def selLimbs (m : BitVec 64) : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | a :: as, b :: bs => ((a &&& m) ||| (b &&& ~~~m)) :: selLimbs m as bs
  | _, _ => []

/-- Base-`2^64` little-endian digits of `n` in exactly `k` limbs (little-endian):
    split the limb count at `h = k / 2`, take the low `h` limbs from `n % 2^(64h)`
    and the high `k - h` limbs from `n / 2^(64h)`. One big-`Nat` division per
    recursion level and `O(log k)` levels, versus one division per limb. -/
def toLimbs : Nat → Nat → List (BitVec 64)
  | _, 0 => []
  | n, 1 => [BitVec.ofNat 64 n]
  | n, (k + 2) =>
    let k' := k + 2
    let h := k' / 2
    let shift := (1 <<< (64 * h) : Nat)
    toLimbs (n % shift) h ++ toLimbs (n / shift) (k' - h)
termination_by _ k => k
decreasing_by
  · omega
  · omega

/-- Base-`2^64` little-endian digits of a `Nat`, balanced radix split. The limb
    count of a nonzero `n` is `Nat.log2 n / 64 + 1`, so the top limb is nonzero
    and the result carries no trailing zero limbs, matching `ofNat`. -/
def ofNatFast (n : Nat) : List (BitVec 64) :=
  if n = 0 then []
  else toLimbs n (Nat.log2 n / 64 + 1)

/-- Base-`2^64` little-endian digits of a `Nat`. The logical body strips one limb
    per step; the compiled body is `ofNatFast`, which computes the same digit list
    by a balanced radix split. -/
@[implemented_by ofNatFast]
def ofNat (n : Nat) : List (BitVec 64) :=
  if h : n = 0 then []
  else BitVec.ofNat 64 (n % 2 ^ 64) :: ofNat (n / 2 ^ 64)
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Strip trailing (high) zero limbs to the canonical form. -/
def norm : List (BitVec 64) → List (BitVec 64)
  | [] => []
  | x :: xs =>
    match norm xs with
    | [] => if x == 0 then [] else [x]
    | y :: ys => x :: y :: ys

/-! ### Carrier operations -/

/-- Carrier addition: the schoolbook add-with-carry chain (any limb lengths). -/
def add (a b : List (BitVec 64)) : List (BitVec 64) := bnAdd a b 0

/-- Carrier multiplication: full schoolbook multiply. -/
def mul (a b : List (BitVec 64)) : List (BitVec 64) := mulBignum a b

/-- Carrier saturating subtraction (exact for equal-length operands): the
    two's-complement difference, selecting zero on borrow. -/
def satSub (a b : List (BitVec 64)) : List (BitVec 64) :=
  let d := subLimbs a b
  selLimbs (0 - d.getLastD 0) d.dropLast (List.replicate a.length 0)

/-- The carrier-add output length: one limb wider than the wider operand. -/
theorem bnAdd_length : ∀ (xs ys : List (BitVec 64)) (c : BitVec 64),
    (bnAdd xs ys c).length = max xs.length ys.length + 1
  | [], [], _ => by simp [bnAdd]
  | [], y :: ys, c => by
      have ih := bnAdd_length [] ys (bSltu (y + c) y)
      simp only [bnAdd, List.length_cons, List.length_nil] at *; omega
  | x :: xs, [], c => by
      have ih := bnAdd_length xs [] (bSltu (x + c) x)
      simp only [bnAdd, List.length_cons, List.length_nil] at *; omega
  | x :: xs, y :: ys, c => by
      have ih := bnAdd_length xs ys (bSltu (x + y) x + bSltu (x + y + c) (x + y))
      simp only [bnAdd, List.length_cons] at *; omega

theorem add_length (a b : List (BitVec 64)) :
    (add a b).length = max a.length b.length + 1 := by
  simp only [add]; exact bnAdd_length a b 0

/-- Exact (truncating) carrier subtraction, padding operands to a common length. -/
def bnSub (a b : List (BitVec 64)) : List (BitVec 64) :=
  satSub (a ++ List.replicate (max a.length b.length - a.length) 0)
         (b ++ List.replicate (max a.length b.length - b.length) 0)

/-- Whole-limb left shift: prepend `m` zero limbs. -/
def shiftBy (m : Nat) (xs : List (BitVec 64)) : List (BitVec 64) :=
  List.replicate m 0 ++ xs

/-- Recursive integer Karatsuba multiplication. Below the crossover (wider
    operand under 16 limbs) it uses the schoolbook `mul`; otherwise it splits at
    the half-limb point, recurses on three sub-products, and recombines. -/
def karatsuba (a b : List (BitVec 64)) : List (BitVec 64) :=
  let n := max a.length b.length
  if h : n < 16 then mul a b
  else
    let m := n / 2
    let a0 := a.take m
    let a1 := a.drop m
    let b0 := b.take m
    let b1 := b.drop m
    let z0 := karatsuba a0 b0
    let z2 := karatsuba a1 b1
    let z1 := bnSub (bnSub (karatsuba (add a0 a1) (add b0 b1)) z0) z2
    add z0 (add (shiftBy m z1) (shiftBy (2 * m) z2))
termination_by max a.length b.length
decreasing_by
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega
  · simp only [add_length, List.length_take, List.length_drop]; omega

/-- Size-dispatched multiply: the Karatsuba recursion. -/
def mulDispatch (a b : List (BitVec 64)) : List (BitVec 64) := karatsuba a b

/-- Left shift of the carrier value by `y` bits. -/
def shl (a : List (BitVec 64)) (y : Nat) : List (BitVec 64) :=
  List.replicate (y / 64) 0 ++ ofNat (bignumVal a * 2 ^ (y % 64))

/-- Right shift of the carrier value by `y` bits. -/
def shr (a : List (BitVec 64)) (y : Nat) : List (BitVec 64) :=
  ofNat (bignumVal (a.drop (y / 64)) / 2 ^ (y % 64))

/-- Bitwise AND of two limb lists: pad to a common length, then limb-wise AND. -/
def land (a b : List (BitVec 64)) : List (BitVec 64) :=
  let n := max a.length b.length
  List.zipWith (· &&& ·) (a ++ List.replicate (n - a.length) 0)
    (b ++ List.replicate (n - b.length) 0)

/-- Bitwise OR of two limb lists: pad to a common length, then limb-wise OR. -/
def lor (a b : List (BitVec 64)) : List (BitVec 64) :=
  let n := max a.length b.length
  List.zipWith (· ||| ·) (a ++ List.replicate (n - a.length) 0)
    (b ++ List.replicate (n - b.length) 0)

/-- Bitwise XOR of two limb lists: pad to a common length, then limb-wise XOR. -/
def xorLimbs (a b : List (BitVec 64)) : List (BitVec 64) :=
  let n := max a.length b.length
  List.zipWith (· ^^^ ·) (a ++ List.replicate (n - a.length) 0)
    (b ++ List.replicate (n - b.length) 0)

/-- Square-and-multiply exponentiation over the verified Karatsuba multiply. -/
def powLimbs (base : List (BitVec 64)) : Nat → List (BitVec 64) → List (BitVec 64)
  | 0, acc => acc
  | (n + 1), acc =>
      let e := n + 1
      let acc' := if e % 2 == 1 then mulDispatch acc base else acc
      powLimbs (mulDispatch base base) (e / 2) acc'
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- Single-limb long division of a little-endian limb list by one limb `d`,
    returning the little-endian quotient limbs and the single-limb remainder.
    The higher limbs are divided first; the returned remainder is folded with the
    current limb `l` into a `128 / 64 → 64` window (`BitVec 128` `udiv`/`umod`, the
    hardware `div r/m64` step), so the kernel is limb-native and does not delegate
    to a `Nat` big-integer division. For `d = 0` the `BitVec` division convention
    applies; the routed operations exclude that case. -/
def divmodLE : List (BitVec 64) → BitVec 64 → List (BitVec 64) × BitVec 64
  | [], _ => ([], 0)
  | l :: ls, d =>
      let (qhi, rhi) := divmodLE ls d
      let w : BitVec 128 := (BitVec.setWidth 128 rhi <<< (64 : Nat)) + BitVec.setWidth 128 l
      let d128 : BitVec 128 := BitVec.setWidth 128 d
      (BitVec.setWidth 64 (w / d128) :: qhi, BitVec.setWidth 64 (w % d128))

/-! ## The routed `Nat` operations

Each `*Impl` runs the verified limb path; each `verifiedNat*` has the plain `Nat`
operation as its logical body and the `*Impl` as its `@[implemented_by]` compiled
body. -/

def verifiedNatAddImpl (a b : Nat) : Nat := bignumVal (add (ofNat a) (ofNat b))
def verifiedNatSubImpl (a b : Nat) : Nat := bignumVal (bnSub (ofNat a) (ofNat b))
def verifiedNatMulImpl (a b : Nat) : Nat := bignumVal (mulDispatch (ofNat a) (ofNat b))
def verifiedNatPowImpl (a b : Nat) : Nat := bignumVal (powLimbs (ofNat a) b (ofNat 1))
def verifiedNatShiftLeftImpl (a b : Nat) : Nat := bignumVal (shl (ofNat a) b)
def verifiedNatShiftRightImpl (a b : Nat) : Nat := bignumVal (shr (ofNat a) b)
def verifiedNatLandImpl (a b : Nat) : Nat := bignumVal (land (ofNat a) (ofNat b))
def verifiedNatLorImpl (a b : Nat) : Nat := bignumVal (lor (ofNat a) (ofNat b))
def verifiedNatXorImpl (a b : Nat) : Nat := bignumVal (xorLimbs (ofNat a) (ofNat b))

/-- Quotient. For a single-limb divisor (`b < 2 ^ 64`) the limb-native
    `divmodLE` computes the quotient digits; for a multi-limb divisor there is no
    vendored limb kernel (Knuth-D is out of scope), so it falls back to `Nat.div`.
    `b = 0` returns `0`, matching `Nat.div a 0`. -/
def verifiedNatDivImpl (a b : Nat) : Nat :=
  if b = 0 then 0
  else if b < 2 ^ 64 then bignumVal (divmodLE (ofNat a) (BitVec.ofNat 64 b)).1
  else a / b

/-- Remainder. For a single-limb divisor (`b < 2 ^ 64`) the limb-native
    `divmodLE` computes the remainder; for a multi-limb divisor it falls back to
    `Nat.mod`. `b = 0` returns `a`, matching `Nat.mod a 0`. -/
def verifiedNatModImpl (a b : Nat) : Nat :=
  if b = 0 then a
  else if b < 2 ^ 64 then (divmodLE (ofNat a) (BitVec.ofNat 64 b)).2.toNat
  else a % b

/-- Euclid recursion structured on an explicit fuel bound so it is manifestly
    terminating; `a + 1` steps bound the descent, so the `fuel = 0` case is
    unreachable. Each step takes the remainder through `verifiedNatModImpl`. -/
def gcdImplAux : Nat → Nat → Nat → Nat
  | 0, _, b => b
  | (fuel + 1), a, b => if a = 0 then b else gcdImplAux fuel (verifiedNatModImpl b a) a

/-- Greatest common divisor via the Euclidean algorithm over the routed
    remainder. Mirrors `Nat.gcd a b = if a = 0 then b else Nat.gcd (b % a) a`. -/
def verifiedNatGcdImpl (a b : Nat) : Nat := gcdImplAux (a + 1) a b

/-- `a == b` via limb-list equality of the canonical digit expansions. -/
def verifiedNatBeqImpl (a b : Nat) : Bool := ofNat a == ofNat b

/-- `a ≤ b` via the verified truncating subtraction: `a ≤ b ↔ a - b = 0`, and a
    value of `0` normalizes to the empty limb list. -/
def verifiedNatBleImpl (a b : Nat) : Bool :=
  norm (bnSub (ofNat a) (ofNat b)) == ([] : List (BitVec 64))

@[implemented_by verifiedNatAddImpl]
def verifiedNatAdd (a b : Nat) : Nat := a + b

@[implemented_by verifiedNatSubImpl]
def verifiedNatSub (a b : Nat) : Nat := a - b

@[implemented_by verifiedNatMulImpl]
def verifiedNatMul (a b : Nat) : Nat := a * b

@[implemented_by verifiedNatPowImpl]
def verifiedNatPow (a b : Nat) : Nat := a ^ b

@[implemented_by verifiedNatShiftLeftImpl]
def verifiedNatShiftLeft (a b : Nat) : Nat := a <<< b

@[implemented_by verifiedNatShiftRightImpl]
def verifiedNatShiftRight (a b : Nat) : Nat := a >>> b

@[implemented_by verifiedNatLandImpl]
def verifiedNatLand (a b : Nat) : Nat := a &&& b

@[implemented_by verifiedNatLorImpl]
def verifiedNatLor (a b : Nat) : Nat := a ||| b

@[implemented_by verifiedNatXorImpl]
def verifiedNatXor (a b : Nat) : Nat := a ^^^ b

@[implemented_by verifiedNatDivImpl]
def verifiedNatDiv (a b : Nat) : Nat := a / b

@[implemented_by verifiedNatModImpl]
def verifiedNatMod (a b : Nat) : Nat := a % b

@[implemented_by verifiedNatGcdImpl]
def verifiedNatGcd (a b : Nat) : Nat := Nat.gcd a b

@[implemented_by verifiedNatBeqImpl]
def verifiedNatBeq (a b : Nat) : Bool := Nat.beq a b

@[implemented_by verifiedNatBleImpl]
def verifiedNatBle (a b : Nat) : Bool := Nat.ble a b

/-! ## Logical correctness (definitional): the kernel sees the intended op. -/

example (a b : Nat) : verifiedNatAdd a b = a + b := rfl
example (a b : Nat) : verifiedNatSub a b = a - b := rfl
example (a b : Nat) : verifiedNatMul a b = a * b := rfl
example (a b : Nat) : verifiedNatPow a b = a ^ b := rfl
example (a b : Nat) : verifiedNatShiftLeft a b = a <<< b := rfl
example (a b : Nat) : verifiedNatShiftRight a b = a >>> b := rfl
example (a b : Nat) : verifiedNatLand a b = a &&& b := rfl
example (a b : Nat) : verifiedNatLor a b = a ||| b := rfl
example (a b : Nat) : verifiedNatXor a b = a ^^^ b := rfl
example (a b : Nat) : verifiedNatDiv a b = a / b := rfl
example (a b : Nat) : verifiedNatMod a b = a % b := rfl
example (a b : Nat) : verifiedNatGcd a b = Nat.gcd a b := rfl
example (a b : Nat) : verifiedNatBeq a b = Nat.beq a b := rfl
example (a b : Nat) : verifiedNatBle a b = Nat.ble a b := rfl

end VerifiedNat
