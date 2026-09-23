# Verified arithmetic for `Nat` literals

The Lean kernel reduces a closed operation on `Nat` literals by computing its value: when it
checks `2 ^ 4096 * 3 = …` by `rfl` or `decide +kernel`, it evaluates the product. The C++
kernel does this with GMP, and upstream lean4lean with Lean's `Nat` operations, which also
run GMP. This fork computes the value with limb kernels written in Lean, next to proofs that
they compute the `Nat` operation.

## The seam

`reduceNat` and `reducePow` in `Lean4Lean/TypeChecker.lean` reduce the fourteen binary
operations with an external implementation (add, sub, mul, pow, div, mod, gcd, shiftLeft,
shiftRight, land, lor, xor, beq, ble); `Nat.succ` is `v + 1`. When both operands are below
`2 ^ 64` (`bothWord`), the one-word `Nat` operation computes the value. Otherwise:

* add, sub, mul, pow, the shifts, the bitwise operations, beq and ble run their
  `Array UInt64` kernel on the limb arrays of the operands. The checker state caches up to
  4096 limb arrays of converted literals (`TypeChecker.State.natLimbs`); a cached array
  carries the proof that it is `ofNatA` of its literal, so a hit is the canonical array;
* div, mod and gcd call `VerifiedNat.verifiedNat<Op>`, whose logical body is the `Nat`
  operation (equal to it by `rfl`) and whose compiled body (`@[implemented_by]`) converts
  to `List (BitVec 64)` limbs, runs the kernel and converts back.

## The kernels

| Operations | Carrier | Module |
|---|---|---|
| add, sub, mul, pow, shiftLeft, shiftRight, land, lor, xor, beq, ble | `Array UInt64` | `VerifiedNatArray.lean`, `VerifiedNatArith.lean` |
| div, mod, gcd | `List (BitVec 64)` | `VerifiedNat.lean` |

Multiplication is schoolbook into a result array updated in place, with the double-word
limb product computed from four `32 × 32`-bit products; pow is square-and-multiply over it.
Division by a one-limb divisor is the long division `divmodLE`,
with a `128 / 64` step per limb; by a multi-limb divisor it is Knuth's Algorithm D
(`divModLimbs`), whose quotient-digit estimate is the same `128 / 64` step followed by at most
two corrections. gcd is the Euclidean algorithm over the routed mod.

## Value theorems

For the `Array UInt64` operations,

* `VerifiedNatArith.lean` and `VerifiedNatArray.lean` prove `toNatA (opA x y) = toNatA x op
  toNatA y` for all limb arrays `x` and `y` for add, sub (truncated), mul, pow, the shifts,
  land, lor and xor, from loop invariants over the low limbs;
* `VerifiedNatArrayProofs.lean` proves `toNatA (opA (ofNatA a) (ofNatA b)) = a op b`, and
* `verifiedNat<Op>Impl a b = a op b`: the compiled body equals the logical body, for add,
  sub, mul, pow, shiftLeft, shiftRight, land, lor, xor, beq and ble, and for div and mod by a
  power of two.

The `List` kernels are the kernels of the CatCrypt development, where each carries a value
theorem against `bignumVal`.

## Tests and demo

`Lean4Lean/Tests/VerifiedNatArrayTest.lean` compares every routed operation with the `Nat`
operation on word boundaries, mixed limb counts, 1000-bit values, shift counts across the
limb boundary and exponents up to 1000. `Demo/VerifiedNat.lean` states facts about numbers of
up to 8192 bits and is checked by

```
lake build Demo lean4lean
lake env .lake/build/bin/lean4lean Demo.VerifiedNat
```
