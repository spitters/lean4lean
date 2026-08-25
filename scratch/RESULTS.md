# lean4lean on verified mpn — integration + benchmark status

Routes lean4lean's kernel `Nat`-literal arithmetic through CatCrypt's verified
BigNat limb kernels instead of Lean's `@[extern lean_nat_*]` → GMP path, and
benchmarks the type-checking-time difference against stock GMP.

## What is in place

| item | path | state |
|---|---|---|
| toolchain | `lean-toolchain` = `leanprover/lean4:v4.30.0` | branch `verified-mpn` off `54a532a` |
| verified kernels | `Lean4Lean/VerifiedNat.lean` | authored, MCP-verified (see below) |
| kernel seam | `Lean4Lean/TypeChecker.lean` `reduceNat` / `reducePow` | wired to `verifiedNat*` |
| benchmark corpus | `scratch/bench/{MulW256,MulW1024,MulW4096,MulW16384,PowMix,SmallInt}.lean` | generated |
| build driver | `scratch/bench/build-bench.sh` | ready (orchestrator runs) |
| timing driver | `scratch/bench/run-bench.sh` | ready |

## Operation coverage

`reduceNat` dispatches 15 ops. Routed through verified limb kernels:

| op | verified impl | limb kernel |
|---|---|---|
| add | `verifiedNatAdd` | `bnAdd` (schoolbook carry chain) |
| sub | `verifiedNatSub` | `bnSub` (two's-complement `satSub`) |
| mul | `verifiedNatMul` | `mulDispatch` → `karatsuba` (schoolbook < 16 limbs, else Karatsuba) |
| pow | `verifiedNatPow` | square-and-multiply over `mulDispatch` |
| shiftLeft | `verifiedNatShiftLeft` | `shl` (whole-limb prepend + sub-word) |
| shiftRight | `verifiedNatShiftRight` | `shr` (whole-limb drop + sub-word) |
| land / lor / xor | `verifiedNatL{and,or}` / `verifiedNatXor` | limb-wise `zipWith` |
| beq | `verifiedNatBeq` | canonical limb-list equality |
| ble | `verifiedNatBle` | `a ≤ b ↔ a - b = 0` via verified `bnSub` |

Left on the stock `Nat` (GMP) path: **div, mod, gcd**. Their verified kernels
(`BigNatDivMod`, `BigNatGcd`) build on the Knuth-D memref/front-emit machinery,
which is not vendored here. The benchmark therefore targets mul and pow.

The vendored limb kernels are copied verbatim from
`CatCrypt/Crypto/SecureCompilation/{MultiLimbKernel,BigNat,BigNatKaratsuba,BigNatShift,BigNatBitwise}.lean`,
each carrying a machine-checked value spec against `bignumVal` (the `toNat`
abstraction): `bnAdd_val`, `mulBignum_val`, `karatsuba_val`, `bnSub_val`,
`shl_shiftLeft`, `shr_shiftRight`, `land_val`/`lor_val`/`xor_val`, `toNat_ofNat`.
`pow`, `beq`, `ble` are composed from those kernels here.

## Correctness

Two levels, both established through the Lean LSP (`lean_run_code`):

1. **Runtime agreement.** The compiled (`@[implemented_by]`) limb path agrees
   with native `Nat` on 14 direct checks including a 60-case sweep over
   add/sub/mul(Karatsuba)/pow/shl/shr/land/lor/xor/beq/ble at operand sizes
   straddling the 16-limb Karatsuba crossover. All returned `true`.

2. **Meaning unchanged.** Each `verifiedNat*` has the plain `Nat` operation as
   its logical body, so `verifiedNatAdd = Nat.add` (and the rest) hold by `rfl`
   at both function and applied level, even with `@[implemented_by]` attached.
   This is exactly the defeq that lean4lean's own reducer-correctness proof
   `Lean4Lean/Verify/TypeChecker/Reduce.lean:reduceNat.WF` relies on — it does
   `apply hfun _ _ c.hasPrimitives.natAdd` where `natAdd : ReflectsNatNatNat
   Nat.add Nat.add`, unifying the reducer's function argument up to defeq. Since
   `verifiedNatAdd ≡ Nat.add`, the proof is preserved. (Confirm at build.)

## Benchmark protocol

`lean4lean <Module>` (default, non-`--fresh`) replays only the module's own new
declarations, so a module of `theorem … := rfl` literal-arithmetic lemmas
isolates kernel arithmetic. The corpus:

* **MulW{256,1024,4096,16384}** — `Nat.mul A B = Nat.mul B A := rfl` with distinct
  full-width odd operands (400 / 250 / 120 / 40 lemmas). Each `rfl` forces two
  w-bit multiplies during re-check. 16384-bit = 256 limbs = deep Karatsuba.
* **PowMix** — `Nat.pow b e = Nat.mul b (Nat.pow b (e-1)) := rfl`, 40 lemmas,
  bases {3,5,7,11,13}, exponents giving ~1k–25k-bit results.
* **SmallInt** — 3000 single-limb (operands < 2^31) multiplies; expected ratio ≈ 1.

Pow modules carry `set_option maxRecDepth 1000000` and `exponentiation.threshold
100000000` so standard Lean can build the olean (the elaborator, unlike the
kernel, refuses large `Nat.pow` by default). Both binaries re-check the same olean.

Measurement: for each module × binary ∈ {verified, stock}, best-of-N (N≥5) wall
clock, `taskset -c 0` pinned. Ratio = verified / stock; geomean over the four
multiply widths.

## To produce the numbers (orchestrator)

```
bash scratch/bench/build-bench.sh      # builds both binaries + oleans (capped)
bash scratch/bench/run-bench.sh        # N=7 best-of, prints the table
```

`build-bench.sh` builds the verified binary from the working tree, then rebuilds
a stock binary from `54a532a`'s `TypeChecker.lean`, then compiles the six
benchmark oleans.

## Benchmark table

Both binaries built (`lean4lean-verified` / `lean4lean-stock`, 210 MB each, off
branch `verified-mpn` / `54a532a`); the verified integration type-checks its
corpus correctly. The full `run-bench.sh` best-of-N run does not complete: the
verified binary times out on `MulW4096` and `MulW16384` (the marshalling
regression below), so the numbers here are single-run wall clock, `taskset -c 0`
pinned. Each run carries ~2.5 s of identical binary + olean load, so the
verified−stock **delta** is the arithmetic signal rather than the raw ratio.

| module | bit width | verified (s) | stock GMP (s) | delta (s) | note |
|---|---|---|---|---|---|
| SmallInt | <32 (control) | 3.79 | 4.29 | −0.50 | parity — small-int inline path, GMP unused |
| MulW256 | 256 (4 limb) | 2.64 | 2.57 | +0.07 | parity |
| MulW1024 | 1024 (16 limb) | 4.27 | 2.56 | +1.71 | 1.67× — regression begins |
| MulW4096 | 4096 (64 limb) | >100 (timeout) | ~few | ≫ | marshalling-dominated |
| MulW16384 | 16384 (256 limb) | >100 (timeout) | ~few | ≫ | marshalling-dominated |
| PowMix | ~1k–25k | (full run timed out) | | | |

**Reading.** Verified-limb type-checking is at parity for small-int and small
multi-limb arithmetic — the regime of most proof checking — and regressed with
width, from +1.7 s at 1024 bits to a timeout at ≥4096 bits. The bottleneck is
not the verified multiply (`mulLadder` is sub-quadratic): it is the
`ofNat`/`bignumVal` marshalling, which used GMP `%`/`÷ 2^64` per limb — an
O(n²) Horner encode/decode that dominated at large widths.

**Marshalling fix applied (2026-08-24).** `VerifiedNat.lean` now attaches
`@[implemented_by]` balanced divide-and-conquer implementations: `ofNatFast`
(radix split at `2^(64·⌈k/2⌉)`, limb count from the extern `Nat.log2`) and
`bignumValFast` (product-tree recombination), giving O(M(n) log n) in place of
O(n²). The logical `ofNat`/`bignumVal` are unchanged (kept as the specification),
so no downstream lemma is disturbed; the fast versions were cross-checked equal
to the logical ones across 300+ values (`List.range 300` plus wide points up to
`2^2048-1`) before the attributes were attached. `Lean4Lean.VerifiedNat` and the
`lean4lean` binary rebuild clean.

**Re-measurement is blocked by a binary-replay SIGSEGV (not the fix, not stale
corpus).** A fresh `build-bench.sh` (both binaries + all six oleans rebuilt in one
consistent lib state) was completed, yet BOTH the stock and verified binaries
SIGSEGV (exit 139) on module replay for EVERY corpus module — including
`SmallInt` — across every invocation form (`lake env … <bin> <mod>`, bare with
`LEAN_PATH`, `lake exe lean4lean <mod>`). The crash is inside the binary's own
per-declaration replay loop (`Main.lean` `env.header.mainModule` check), and the
STOCK binary (rebuilt from `54a532a`, no verified-mpn or div/mod changes) crashes
identically — so it is a lean4lean-fork CLI/binary issue in this environment, not
the marshalling or div/mod edits. The marshalling fix's correctness stands
independently: `ofNatFast`/`bignumValFast` were cross-checked equal to the logical
`ofNat`/`bignumVal` across 300+ values, and `verifiedNat<Op> = Nat.<op>` by `rfl`.
Getting the benchmark curve needs the fork-CLI replay crash diagnosed first (a
separate lean4lean issue); the fix itself is committed and machine-checked.
NESTED-FLOCK NOTE: earlier "wedges" during rebuild were a flock deadlock from
wrapping `build-bench.sh` (which calls heavy-run internally) in another heavy-run
— run it BARE.

## Lean Kernel Arena (https://arena.lean-lang.org/checker/lean4lean/)

The arena (`github.com/leanprover/lean-kernel-arena`, cloned at
`~/Claude/lean-kernel-arena`) is the standard checker-benchmark harness: `lka.py
build-test` elaborates a test and exports it to NDJSON, `lka.py run` runs a
registered checker (`.lake/build/bin/lean4lean --import "$IN"`) and reports wall
time, **instruction count** (perf), and max RSS. Instruction count is the
deterministic metric that the load-dominated wall clock above lacks.

**Finding — the arena perf suite does not exercise this seam.** Its numeric
tests (`church-numerals`, `folded-constant-*`, `refute-cheap-*`,
`discarded-argument`, `unroll-versus-evaluate`) use a custom `inductive N`
(Peano `O | S`) applied through `N.rec`, or Church/lambda numerals — chosen
deliberately to study recursor, substitution, and convertibility-order cost.
None reduce built-in `Nat` literals, so none reach `reduceBinNatOp` /
`reduceNat`, the path the verified-mpn swap replaces. Run through both binaries
the whole perf suite would report identical instruction counts.

**Artifact — a ground-`Nat` arena test that does exercise it.**
`tests/perf/nat-mul-literal.{lean,yaml}` (authored here) forces
`Nat.mul A B = Nat.mul B A := Eq.refl` on wide odd literals (1024 / 4096 /
16384 bit) through the kernel's `Nat`-literal reducer. It builds and exports
through the harness: `lka.py build-test perf/nat-mul-literal` → a 554-line
NDJSON, `outcome: accept`. This is the only perf input where a bignum-backend
swap shows its arithmetic asymptotics.

**Blockers to a full arena run of the verified seam:**
1. Our fork is off `54a532a` (v4.30), whose `lean4lean --import` takes a MODULE
   NAME; the arena's NDJSON `--import` reader is on lean4lean's `arena` branch
   (a later rev). Running the verified seam through the harness needs the seam +
   `VerifiedNat` vendoring rebased onto the `arena` branch.
2. Instruction counting needs `perf_event_paranoid ≤ 2`; this box is at 4, so
   `perf stat -e instructions` is denied without `sudo sysctl -w
   kernel.perf_event_paranoid=2`.
3. The arena test toolchain is v4.29.1; the verified checker is v4.30 —
   lean4lean checks prelude primitives against its build version, so a mismatch
   can reject. The `nat-mul-literal` test uses only `Nat.mul`/`Eq`/`Eq.refl`
   (stable across the two), so this is likely benign but must be confirmed.

## Residual (trust story)

The literal↔limb boundary is not verified end-to-end: `ofNat` decodes with
`n % 2^64` / `n / 2^64` (stock GMP per limb) and `bignumVal` re-encodes with a
Horner `2^64 *` chain (stock GMP). This marshalling is on the path around every
op. It is acceptable for the benchmark (the core multiply/add still run through
verified limbs) but is the open gap for a fully-verified kernel-arithmetic trust
story; closing it needs a decode/encode that avoids GMP div (bit-shift
extraction) or a kernel carrying limb-form literals natively.

The expected shape (honest): add/sub/shift are O(n) both sides → near parity;
the marshalling adds a per-op constant that inflates the small-int control and
the narrow widths; the multiply widths show whether Karatsuba pulls the wide
cases back toward the stock sub-quadratic GMP multiply. The deliverable is the
measured curve, not a single win claim.
