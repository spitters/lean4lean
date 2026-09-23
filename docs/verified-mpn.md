# Verified-mpn: verified arithmetic in the lean4lean kernel

This branch replaces the arithmetic backend of lean4lean's `Nat`-literal
reduction. Where the kernel would reduce a closed `Nat` operation by calling
Lean's `Nat.add`/`Nat.mul`/… (which run GMP through `@[extern lean_nat_*]`), it
instead runs a verified little-endian base-`2^64` limb kernel. The result is a
proof checker whose definitional-reduction arithmetic is verified limb code
rather than trusted GMP.

## Why lean4lean, and why the kernel and not the compiler

The claim being exercised is about the **kernel** — the trusted proof checker —
specifically its definitional reduction on the `rfl`/`decide` type-checking
path. When the kernel checks `Nat.mul A B = Nat.mul B A := rfl`, it reduces both
sides to normal form and compares; that reduction runs `reduceNat` in
`whnf`/`isDefEq`, which is where the seam sits.

The real C++ Lean kernel reduces `Nat` literals in its own separate compiled
mpz code, which a Lean-level replacement cannot reach. lean4lean, being the
kernel reimplemented in Lean, performs that reduction with Lean's own `Nat`
operations — which `@[implemented_by]` can swap. That is what makes verified
arithmetic in a kernel possible here.

`native_decide` is a different path: it compiles the decision procedure with the
Lean **compiler**, runs it natively, and the kernel accepts the boolean under the
`Lean.ofReduceBool` axiom without calling the reducer. The seam does not touch
`native_decide`. A proof only runs on the verified arithmetic if it is
kernel-checked (`decide`/`rfl`).

## What is implemented

Branch `verified-mpn-4.31`, based on upstream `095c0a9` (`v4.31.0`).

- **`Lean4Lean/VerifiedNat.lean`** — vendored pure-core limb kernels
  (`List (BitVec 64)` + `BitVec`, no Mathlib) and, for each kernel `Nat`
  operation, a `verifiedNat*` whose logical body is the plain `Nat` op (equal to
  it by `rfl`) and whose `@[implemented_by]` compiled body decodes to limbs, runs
  the limb kernel, and re-encodes. Covered: `add`, `sub`, `mul` (Karatsuba
  dispatch), `pow` (square-and-multiply), `div`, `mod`, `gcd`, `shiftLeft`,
  `shiftRight`, `land`, `lor`, `xor`, `beq`, `ble`.
- **`Lean4Lean/TypeChecker.lean`** — the seam: `reduceNat` and `reducePow`
  dispatch each `Nat.op` through the matching `VerifiedNat.verifiedNat*` (import
  plus fifteen substitutions; the surrounding reduction is unchanged).
- **Single-word gate** — each binary `*Impl` defers to the native `Nat` op when
  both operands are below `2^64`. A single machine word never enters GMP's
  multi-limb code, so the verified path adds no assurance there and only
  marshalling overhead. The gate makes small-integer reduction (the bulk of real
  proof-checking) native, and the verified path runs exactly where GMP's
  multi-limb code would.
- **Multi-limb division (Knuth Algorithm D, `divModLimbs`)** — for a divisor of
  two or more limbs. The quotient-digit estimate is a `128/64` hardware division
  (`BitVec 128` udiv, the same limb-native step as the single-limb `divmodLE`),
  never a `Nat` big-division; correction is at most two decrements, with a
  multiply-subtract and a rare add-back per digit. With this, all fifteen
  operations route through verified limbs and no GMP fallback remains.

## Build and benchmark

```
# both on the v4.31.0 toolchain (installed via elan)
lake build lean4lean:exe
```

Two binaries are compared: `scratch/bench/lean4lean-verified` (this branch) and
`scratch/bench/lean4lean-stock` (the same base with the seam reverted, pure GMP).
Each type-checks the same `.olean`; only the reducer's arithmetic differs.
`scratch/bench/run431.sh` runs the width sweep; `scratch/bench/gen_modmul.lean`
generates the modmul modules; `scratch/bench/Profile.lean` profiles one multiply;
`scratch/bench/DivProto.lean` is the division KAT.

## Results (kernel type-checking wall time, best of three)

Full tables in `scratch/bench/RESULTS-4.31.md`. Verified/stock ratio:

| workload                       | limbs | ratio |
|--------------------------------|-------|-------|
| small integers                 | ≤1    | ~1.0× |
| multiply, 256-bit              | 4     | 1.3×  |
| multiply, 1024-bit             | 16    | 3.6×  |
| multiply, 4096-bit             | 64    | 15.8× |
| multiply, 16384-bit            | 256   | ~50×  |
| modmul (P-384)                 | 6     | 2.2×  |
| modmul (P-521)                 | 9     | 3.5×  |
| modmul (RSA-2048)              | 32    | 15.8× |

Parity on small and typical arithmetic; the regression grows with width. The 50×
figure is a 16384-bit number — no cryptographic prime is that large. A
kernel-checked prime certificate at curve sizes (4–9 limbs) type-checks at
2–3.5×, with both the multiplications and the modular reductions verified.

Profiling shows the cost is the multiply, not the plumbing: at 256 limbs the
`Nat`↔limb marshalling is ~0.3% of one multiply and the list-based Karatsuba is
the rest. The performance lever is the limb representation
(`List (BitVec 64)` → `Array`), not removing marshalling.

## The 4.30 crash

On the `v4.30.0` base, the kernel SIGSEGV'd while replaying modules with wide
`Nat` literals (`lean_dec_ref_cold` in the Lean runtime's large-mpz refcount
path, before the reducer). It is a Lean-runtime bug fixed by the `v4.30 → v4.31`
toolchain, not a lean4lean defect; the whole wide-`Nat` corpus runs clean on
4.31. The fix is the toolchain bump, not a code change.

## Trust status

- Each `verifiedNat* = Nat.op` holds by `rfl` — the kernel sees the intended
  operation. This is the logical body; it says nothing about the compiled impl.
- For most operations the impl-level refinement
  (`bignumVal (kernel (ofNat a) (ofNat b)) = Nat.op a b`) is machine-checked in
  the CatCrypt SSProve development, from the vendored kernels' value
  specifications.
- **`divModLimbs` (Knuth-D) has no refinement proof yet.** Its correctness rests
  on a 1627-case KAT (quotient and remainder, 2–32 limb divisors, edge cases)
  and 6200 kernel-reduced `rfl` lemmas — strong evidence, since a wrong result
  is rejected by the kernel, but not a theorem. Division is one notch below the
  other operations on assurance.
- `@[implemented_by]` bodies are consumed as trusted by the Lean toolchain
  regardless of the refinement proof. The trusted base depends on the proofs
  only in the stronger configuration, where the kernel carries the limb
  representation natively with a proven decode.

## Follow-ups

1. Prove `divModLimbs` correct (`bignumVal (divModLimbs u v).1 = … / …` and the
   remainder analogue), bringing division to parity with the other operations.
2. Change the limb representation to `Array` for the wide-multiply regime; this
   is the measured performance lever, not marshalling.
3. To run a project's primality proofs on verified arithmetic, move them off
   `native_decide` (which bypasses the reducer) to kernel-checked Pratt
   certificates.
