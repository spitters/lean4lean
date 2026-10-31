/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE-MIT.
Authors: CatCrypt Contributors
-/
import Lean4Lean.TypeChecker

/-!
# Evaluation checks for the `Array UInt64` limb operations

Each `#eval` compares the limb operations of `Lean4Lean.VerifiedNatArray` and
`Lean4Lean.VerifiedNatArith`, and the routed `verifiedNat<Op>` functions, with
the `Nat` operations on a fixed set of operands (word boundaries, mixed limb
counts, 1000-bit values), shift counts across the limb boundary, powers with
exponents up to 1000, and power-of-two divisors. The conversion checks cover every
limb count up to 40 and 308 and 1000 limbs, and the last check runs `reduceNat`
with the limb cache of the type checker state. Each prints the list of failing
cases, which is empty when the operations agree.
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

/-! ### Conversions at block boundaries -/

/-- Limb counts for the conversion checks: every count up to 40 (each side of the
    `limbBlock` boundaries) and 308 and 1000. -/
def convLimbCounts : List Nat := List.range 41 ++ [308, 1000]

/-- Values of `k` limbs: all ones, alternating bits, only the top bit, and a
    dense power of three truncated to `k` limbs. -/
def convValues (k : Nat) : List Nat :=
  if k = 0 then [0]
  else [2 ^ (64 * k) - 1, (2 ^ (64 * k) - 1) / 3, 2 ^ (64 * k - 1),
    3 ^ (40 * k) % 2 ^ (64 * k) ||| 2 ^ (64 * k - 2)]

/-- The limb list of `n` computed limb by limb. -/
def refLimbs (n : Nat) : List UInt64 :=
  (List.range (limbCount n)).map fun i => UInt64.ofNat (n >>> (64 * i))

#eval convLimbCounts.flatMap fun k => (convValues k).filter fun n =>
  toNatA (ofNatA n) != n || (ofNatA n).toList != refLimbs n ||
    (ofNatA n).size != k || (ofNatA n).back? == some 0

#eval convLimbCounts.flatMap fun k => (convValues k).filter fun n =>
  normA ((ofNatA n).push 0 |>.push 0) != ofNatA n

end VerifiedNat.Test

/-! ### Reduction with the limb cache -/

namespace Lean4Lean.TypeChecker.Test
open Lean hiding Environment Exception
open Kernel Inner

/-- Methods whose `whnf` is the identity; the reduced expressions are literals. -/
def literalMethods : Methods where
  isDefEqCore _ _ := pure false
  whnfCore e _ _ := pure e
  whnf e := pure e
  inferType e _ := pure e

/-- The application of the binary `Nat` operation `f` to two literals. -/
def natApp (f : Name) (a b : Nat) : Expr :=
  mkApp2 (.const f []) (.lit (.natVal a)) (.lit (.natVal b))

/-- Shift, and, or, xor, add and comparison steps on values of 298 and 308 limbs.
    Several steps share operands, so later steps find them in `State.natLimbs`. -/
def chain : List (Name × Nat × Nat) :=
  let m := 2 ^ 19683 - 1
  let a := 3 ^ 12000
  (List.range 12).map fun i =>
    match i % 6 with
    | 0 => (``Nat.shiftLeft, a + i, 64 * i + 5)
    | 1 => (``Nat.land, a * (i + 1), m)
    | 2 => (``Nat.lor, a, m >>> i)
    | 3 => (``Nat.xor, a + i, m)
    | 4 => (``Nat.add, a, a * 7)
    | _ => (``Nat.ble, a, a + i)

/-- The reference value of one step of `chain` as a literal. -/
def chainRef : Name × Nat × Nat → Expr
  | (f, a, b) =>
    if f == ``Nat.shiftLeft then .lit (.natVal (a <<< b))
    else if f == ``Nat.land then .lit (.natVal (a &&& b))
    else if f == ``Nat.lor then .lit (.natVal (a ||| b))
    else if f == ``Nat.xor then .lit (.natVal (a ^^^ b))
    else if f == ``Nat.add then .lit (.natVal (a + b))
    else toExpr (Nat.ble a b)

/-- Reduce every step of `chain` twice in one state and return the steps whose
    result differs from `chainRef`. The first pass converts operands that are not
    yet cached; the second pass reads every multi-limb operand from the cache, so
    an empty result means cached and uncached reductions agree with `Nat`. -/
def cachedFailures (env : Environment) : Except Exception (List Nat) :=
  M.run env (x := do
    let mut bad : List Nat := []
    for _ in [0, 1] do
      for (s, i) in chain.zip (List.range chain.length) do
        let r ← reduceNat (natApp s.1 s.2.1 s.2.2) literalMethods
        if r != some (chainRef s) then bad := i :: bad
    return bad)

#eval show IO _ from do
  let env := (← mkEmptyEnvironment).toKernelEnv
  return cachedFailures env |>.toOption

end Lean4Lean.TypeChecker.Test
