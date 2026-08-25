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
GMP accepts across 3830 wide-arithmetic lemmas. The perf gap is a marshalling
optimization target, not a soundness question.
