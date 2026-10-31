/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE-MIT.
Authors: CatCrypt Contributors
-/

/-!
# Kernel `Nat` arithmetic on multi-limb literals

Each theorem is closed by `decide +kernel`, so its proof term is `Eq.refl true` at the type
`decide p = true`, and a checker accepts it only by reducing the closed `Nat` operations of
`p` to literals. In every operation at least one operand has between 4 and 129 limbs of 64
bits, so under `lean4lean` the reduction runs the limb kernels of `Lean4Lean.VerifiedNat`
where the C++ kernel runs GMP.

Check this module with

```
lake build Demo
lake env .lake/build/bin/lean4lean Demo.VerifiedNat
```
-/

namespace Demo.VerifiedNat

/-- A product of two 4096-bit numbers. -/
theorem mul_4096 : (2 ^ 4096 + 1) * (2 ^ 4096 - 1) = 2 ^ 8192 - 1 := by decide +kernel

/-- A sum with a carry through 64 limbs. -/
theorem add_carry : (2 ^ 4096 - 1) + 1 = 2 ^ 4096 := by decide +kernel

/-- The gcd of two Mersenne numbers is the Mersenne number of the gcd of the exponents. -/
theorem gcd_mersenne : Nat.gcd (2 ^ 600 - 1) (2 ^ 400 - 1) = 2 ^ 200 - 1 := by decide +kernel

/-- A remainder by a 20-limb divisor. -/
theorem mod_mersenne : 2 ^ 1279 % (2 ^ 1279 - 1) = 1 := by decide +kernel

/-- A quotient by a one-limb divisor, recombined. -/
theorem div_repunit : (10 ^ 1000 - 1) / 9 * 9 + 1 = 10 ^ 1000 := by decide +kernel

/-- Shifts and a mask across the limb boundary. -/
theorem shift_mask :
    (2 ^ 3000 + 5) >>> 2999 = 2 ∧ (2 ^ 3000 + 5) &&& (2 ^ 64 - 1) = 5 ∧
      (2 ^ 3000 + 5) <<< 64 = 2 ^ 3064 + 5 * 2 ^ 64 := by decide +kernel

end Demo.VerifiedNat
