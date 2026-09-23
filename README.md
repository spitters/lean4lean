# Lean-for-Lean

This is an implementation of the Lean 4 kernel written in (mostly) pure Lean 4.
It is derived directly from the C++ kernel implementation, and as such likely
shares some implementation bugs with it (it's not really an independent
implementation), although it also benefits from the same algorithmic performance
improvements existing in the C++ Lean kernel.

The project also houses some metatheory regarding the Lean
system, in the same general direction as the
[MetaCoq project](https://github.com/MetaCoq/metacoq/).

## Building

To compile the code, you will need [Lean](https://lean-lang.org/lean4/doc/quickstart.html), or more specifically `elan`, the Lean version manager, which will make sure you have the right version of lean as specified in the [lean-toolchain](lean-toolchain) file. Assuming you have elan, the project can be compiled with:

```
lake build
```

This builds all components but you can also build them separately:

* `lake build Lean4Lean` builds the `Lean4Lean` library interface, and does not include any of the proofs.
* `lake build lean4lean` (note the capitalization!) builds the `lean4lean` command line tool, again without building proofs.
* `lake build Lean4Lean.Theory` contains the Lean metatheory and properties.
* `lake build Lean4Lean.Verify` is the proof that the `Lean4Lean` implementation satisfies the `Lean4Lean.Theory` abstract specification.

## Running

After `lake build lean4lean`, the executable will be in `.lake/build/bin/lean4lean`. Because it requires some environment variables to be set for search paths which are provided by lake, you should evaluate it like `lake env .lake/build/bin/lean4lean`.

If you run this as is (with no additional arguments), it will check every olean in the `lean4lean` package itself, which is probably not what you want. To check a different Lean package you should navigate the directory of the target project, then use `lake env path/to/lean4lean/.lake/build/bin/lean4lean <args>` to run `lean4lean` in the context of the target project. The command line arguments are:

> `lean4lean [--fresh] [-v|--verbose] [--compare] [--machine-eval] [MOD]`

* `MOD`: an optional lean module name, like `Lean4Lean.Verify`. If provided, the specified module will be checked (single-threaded); otherwise, all modules on the Lean search path will be checked (multithreaded).
* `--fresh`: Only valid when a `MOD` is provided. In this mode, the module and all its imports will be rebuilt from scratch, checking all dependencies of the module. The behavior without the flag is to only check the module itself, assuming all imports are correct.
* `--verbose`: shows the name of each declaration before adding it to the environment. Useful to know if the kernel got stuck on something.
* `--compare`: If lean4lean takes more than a second on a given definition, we also check the C++ kernel performance to see if it is also slow on the same definition and report if lean4lean is abnormally slow in comparison.
* `--machine-eval`: reduce `Lean.reduceBool` applications of the form described in [Machine evaluation](#machine-evaluation) by running machine code; without the flag they are rejected.

## Verified arithmetic and machine evaluation

This fork adds two things to the checker: verified arithmetic for `Nat` literals, and a
reduction rule that evaluates a decision procedure by running its machine code.

### Verified `Nat` arithmetic

The kernel reduces a closed `Nat` operation on literals (`Nat.add`, `Nat.mul`, `Nat.pow`,
`Nat.div`, `Nat.gcd`, the shifts, the bitwise operations, `Nat.beq`, `Nat.ble`: fifteen in
all) by computing its value. Upstream lean4lean computes it with Lean's `Nat` operations,
which run GMP. Here each operation is a function `verifiedNat<Op>` whose logical body is the
`Nat` operation and whose compiled body (`@[implemented_by]`) runs a little-endian base-`2^64`
limb kernel written in Lean:

* when both operands are below `2^64`, the compiled body is the one-word `Nat` operation;
* add, sub, mul, pow, the shifts, land, lor, xor, beq and ble run on an `Array UInt64`
  carrier (`Lean4Lean/VerifiedNatArray.lean`, `VerifiedNatArith.lean`), on limb arrays the
  checker caches for recently converted literals;
* div, mod and gcd run on a `List (BitVec 64)` carrier (`Lean4Lean/VerifiedNat.lean`), with
  Knuth's Algorithm D for multi-limb divisors;
* `Nat.succ` is `v + 1`.

The `Array UInt64` add, sub, mul, pow, shifts, land, lor and xor carry value theorems
`toNatA (opA x y) = toNatA x op toNatA y` for all limb arrays, and
`Lean4Lean/VerifiedNatArrayProofs.lean` proves `verifiedNat<Op>Impl = Nat.<op>` for every
`Array UInt64` operation and for div and mod by a power of two. [`Demo/VerifiedNat.lean`](Demo/VerifiedNat.lean) states six facts about numbers of up
to 8192 bits, closed by `decide +kernel`:

```
lake build Demo lean4lean
lake env .lake/build/bin/lean4lean Demo.VerifiedNat
```

[docs/verified-mpn.md](docs/verified-mpn.md) describes the kernels.

### Machine evaluation

With `--machine-eval`, the checker reduces `Lean.reduceBool c` when the value of `c` is an
application of `machineAcceptsNatD code n h regs regions res` to literals: `code` is x86-64
machine code as a list of byte chunks, `n` its instruction count, `regs` and `regions` the
initial registers and memory, `res` the register holding the answer, and `h` a proof that
`code` decodes to `n` instructions. The checker type-checks `h`, runs the code on the host
processor through the runner named by the environment variable `CATCRYPT_VRUN`, and reduces
`Lean.reduceBool c` to the runner's answer. The rule is `Lean4Lean/MachineEval.lean`; the
runner is [`runner/vrun.c`](runner/vrun.c):

```
cc -O2 -o runner/vrun runner/vrun.c
export CATCRYPT_VRUN=$PWD/runner/vrun
```

The trusted base of a proof checked this way is the checker, the runner and the processor's
execution of the bytes. The proofs are produced by the `verified_decide_lit` tactic of the
CatCrypt development, which compiles a decision procedure from a fragment of Lean to
x86-64 code, proves the compilation correct against a machine model, and emits the
`machineAcceptsNatD` call.

## More documentation

* [bugs-found.md](bugs-found.md): A list of kernel bugs that the lean4lean project has uncovered.
* [divergences.md](divergences.md): A list of deliberate divergences between lean's kernel and the lean4lean kernel.

## (Selected) file breakdown

* `Main.lean`: command line app
* `Lean4Lean`: source files
  * `Environment.lean`: library entry point
  * `TypeChecker.lean`: main recursive function
  * `Inductive`
    * `Add.lean`: constructing inductive recursors
    * `Reduce.lean`: inductive iota rules
  * `Quot.lean`: quotient types handling
  * `Primitive.lean`: checking correctness of built-ins
  * `Std`: stuff that should exist upstream
  * `Theory`: lean metatheory
    * `VLevel.lean`: level expressions
    * `VExpr.lean`: expressions (boring de Bruijn variable theorems are here)
    * `VDecl.lean`: declarations
    * `VEnv.lean`: environment
    * `Meta.lean`: elaborator producing `VExpr`s
    * `Inductive.lean`: inductive types
    * `Quot.lean`: quotient types
    * `Typing`
      * `Basic.lean`: The typing relation itself
      * `Lemmas.lean`: theorems about the typing relation
      * `Meta.lean`: tactic for proving typing judgments
      * `Strong.lean`: proof that you can have all the inductive hypotheses
      * `UniqueTyping.lean`: conjectures about the typing relation
      * `Env.lean`: typing for environments
  * `Verify`: relation between the metatheory and the kernel
    * `Axioms.lean`: theorems about upstream opaques that shouldn't be opaque
    * `Expr.lean`: correctness of basics on `Expr`
    * `Level.lean`: correctness of basics on `Level`
    * `Level/Std.lean`: soundness of the standard-library level operations
    * `VLCtx.lean`: a "translation context" suitable for translating expressions
    * `LocalContext.lean`: properties of lean's `LocalContext` type
    * `NameGenerator.lean`: properties of the fresh name generator
    * `Typing`
      * `Expr.lean`: translating expressions (`TrExpr` is here)
      * `Lemmas.lean`: properties of `TrExpr`
      * `ConditionallyTyped.lean`: properties of expressions in caches that may be out of scope
    * `Environment`
      * `Basic.lean`: translating environments
      * `Lemmas.lean`: properties of `TrEnv`
    * `TypeChecker`
      * `Basic.lean`: typechecker invariants
      * `EquivManager.lean`: invariants for the union-find defeq cache
      * `InferType.lean`: correctness of `inferType`
      * `WHNF.lean`: correctness of `whnf`
      * `IsDefEq.lean`: correctness of `isDefEq`
    * `TypeChecker.lean`: top-level typechecker correctness
  * `Experimental`: work in progress formalizations and ideas
      * `Stratified.lean`: stratified typing judgment
      * `StratifiedUntyped.lean` another stratified typing judgment
      * `ParallelReduction.lean`: stuff related to church-rosser
      * `Stronger.lean`: a more heavily annotated typing judgment
