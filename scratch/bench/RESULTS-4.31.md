# lean4lean verified-mpn benchmark — 4.31 toolchain

Base: upstream `095c0a9` (v4.31.0). Branch `verified-mpn-4.31`: `VerifiedNat.lean`
(vendored limb kernels + `@[implemented_by]` wrappers) + the `TypeChecker.lean`
`reduceNat`/`reducePow` seam routing 15 Nat ops through verified limb code.
The 4.30 SIGSEGV on wide-`Nat` replay is fixed by the toolchain (Lean-runtime
large-mpz refcount fix, 4.30 → 4.31); the whole corpus now runs.

Two binaries, same base, same 4.31 oleans:
- `lean4lean-stock` — pure `Nat.<op>` (GMP)
- `lean4lean-verified` — limb-native seam

Best-of-3 min wall (`scratch/bench/run431.sh`), single box. Correctness cross-check:
both binaries accept the identical declaration count on every completed module.

| module    | width      | decls | stock (GMP) | verified (limb) | ratio v/s | check |
|-----------|------------|-------|-------------|-----------------|-----------|-------|
| SmallInt  | ≤64-bit    | 3000  | 0.47 s      | 0.51 s          | 1.09×     | equal |
| MulW256   | 4-limb     | 400   | 0.33 s      | 0.42 s          | 1.27×     | equal |
| MulW1024  | 16-limb    | 250   | 0.32 s      | 1.23 s          | 3.80×     | equal |
| MulW4096  | 64-limb    | 120   | 0.32 s      | 5.09 s          | 15.93×    | equal |
| MulW16384 | 256-limb   | 40    | 0.31 s      | 15.65 s         | 51.12×    | equal |
| PowMix    | wide pow   | 40    | 0.27 s      | >180 s (t/o)    | —         | —     |

Reading the curve:
- Stock time is flat (~0.3 s) and dominated by binary load + olean replay; GMP's
  mpz multiply at these widths is microseconds, so the stock arithmetic is
  negligible. The wall-clock ratio therefore understates the pure-arithmetic
  factor (subtract the ~0.3 s fixed floor to see it).
- Parity on small/typical arithmetic (SmallInt, MulW256), which is what real
  proof-checking is dominated by.
- The regression grows ~quadratically in width (ratio ≈ ×4 per ×4 limbs). The
  bottleneck is the `ofNat`/`bignumVal` Nat↔limb marshalling done per operation,
  not the multiply (`mulLadder` is sub-quadratic). Balanced marshalling
  (`e34c118`) lets 16384-bit COMPLETE (was a >100 s timeout on 4.30) but has not
  removed the super-linear growth.
- PowMix times out because pow is square-and-multiply over the same wide-mul
  marshalling, compounding it.

Correctness is the headline: the verified kernel accepts exactly the declarations
GMP accepts across 3830 wide-arithmetic lemmas.

## Where the cost is (profiled, per multiply, `Profile.lean`)

At 256 limbs (16384-bit), one `verifiedNatMulImpl`: `ofNat` decode 230 us,
`mulDispatch` (Karatsuba) 173,897 us, `bignumVal` encode 177 us. The Nat<->limb
marshalling is ~0.3% of the cost; the pure-Lean list-based Karatsuba multiply is
~99.7%. Removing marshalling (native limb literals) would save ~0.3%. The perf
lever is the multiply representation (`List (BitVec 64)` with per-limb
allocation), not marshalling.

## Single-word gate

`VerifiedNat` now gates each binary op on `bothWord a b` (both operands < 2^64):
below one limb the native `Nat` op runs word arithmetic without entering GMP, so
the verified limb path adds no assurance and only marshalling overhead. Gated:
SmallInt drops from 1.09x to parity (0.89x); wide widths unchanged.

## Prime-certificate widths (modmul `(A*B) % P = C := rfl`, `gen_modmul.lean`)

The per-step shape of a kernel-checked primality/modexp certificate: a full-width
multiply then a reduction modulo an n-limb modulus (the `mod` falls back to GMP
for a multi-limb divisor, so only the multiply is on the verified path).

| prime      | limbs | modmuls | stock | verified | wall ratio |
|------------|-------|---------|-------|----------|------------|
| P-384      | 6     | 3000    | 0.56s | 1.22s    | 2.16x      |
| ~P-521     | 9     | 2000    | 0.46s | 1.44s    | 3.11x      |
| RSA-2048   | 32    | 800     | 0.34s | 4.84s    | 14.03x     |

All correctness-verified. Curve primes (4-9 limbs) type-check at 2-3x; RSA-2048
(32 limbs) at 14x. The 51x figure is a 256-limb (16384-bit) number, far beyond any
prime. Removing the ~0.2-0.3s binary-load+replay floor, the pure per-modmul
arithmetic ratio is higher (~3.5x at 6 limbs, ~100x at 32 limbs) because GMP's
multiply is optimized asm and ours is list-based Lean; the end-to-end wall stays
2-14x because the load+replay floor is shared.

We benchmark the lean4lean *kernel* (proof checker), specifically its
definitional-reduction `Nat` arithmetic on the `rfl`/`decide` type-checking path
(`reduceNat` in `whnf`/`isDefEq`). Both binaries are the kernel; only the
arithmetic backend differs (GMP vs verified limbs). This is not the compiler:
`native_decide` compiles and runs the check natively and the kernel accepts the
result under `ofReduceBool`, never calling the reducer -- so the seam does not
touch it.

Caveats for the trust story: (1) `native_decide` primality proofs bypass the
kernel reducer entirely, so the verified path applies only to kernel-checked
(`decide`/`rfl`) certificates. (2) [CLOSED] The modular reduction now routes a
multi-limb divisor through Knuth Algorithm D (`divModLimbs`, 128/64 hardware
qhat, no `Nat` big-division), so div and mod are on the verified path with no GMP
fallback. Validated by a 1627-case KAT and 6200 kernel-reduced rfl lemmas. Wall
ratios with the verified mod: 6-limb 2.24x, 9-limb 3.50x, 32-limb 15.78x.
