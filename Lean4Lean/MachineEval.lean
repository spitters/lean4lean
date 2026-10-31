import Lean

/-!
# Machine evaluation of asserted `machineAcceptsNatD` results

In Lean v4.35.0 the kernel has no native reduction (`Lean.reduceBool` and `Lean.reduceNat` are
removed); a result obtained by native evaluation enters the logic as an axiom `e = true`, which is
what `Lean.Meta.nativeEqTrue` (the
basis of `native_decide` and `bv_decide`) adds. The checker, like the kernel, accepts every
well-typed axiom. This module gives the checker one rule that confirms such an axiom by
evaluation instead of accepting it as stated. The rule is active only when
`FuelConfig.machineEval` is set (command-line flag `--machine-eval`, or
`--config:machineEval=true`); with the flag off, `checkAxiom` succeeds without inspecting the
axiom, and axioms are handled exactly as in upstream lean4lean.

An axiom is a machine-evaluation claim when its type is `@Eq.{1} Bool lhs Bool.true` and `lhs`
either has the head constant

  `VerifiedEval.machineAcceptsNatD`

(the shape `nativeEqTrue` produces) or is a constant without universe parameters that is defined
as such an application (the shape of a tactic that names the evaluated term by an auxiliary
definition). `claim?` recognises the two shapes; every other axiom is accepted as upstream
accepts it. A claim is accepted only when its application has the form

  `machineAcceptsNatD chunks n h regs regions res`

where `chunks : List (List Nat)` (the code bytes, in chunks), `regs : List Nat` and
`regions : List (Nat × List Nat)` are closed chains of `List.cons` / `List.nil` / `Prod.mk` (at
universe `0` and at the types `Nat`, `List Nat`, `Prod Nat (List Nat)`) whose leaves are raw
natural-number literals, `n` (the instruction count) and `res` are raw literals, `h` is any
term, which the rule does not inspect, and the machine evaluates the application to `true`.
A claim of any other form, a failed range check, a runner failure or the answer `false` rejects
the axiom.

The machine computes the processor's answer on the concatenated code bytes. The definition of
`machineAcceptsNatD` is `false` when the bytes do not decode into exactly `n` instructions; the
argument `h : codeDecodes chunks n = true` excludes that case. The rule relies on `h` without
decoding: the checker type-checks the axiom's type (and, in the second shape, the value of the
auxiliary definition) before `checkAxiom` runs, so `h` is a checked proof of the decoding fact.
`regs` must have sixteen entries below `2 ^ 64`, `res` must be below `16`, every byte of the code
and of the regions must be below `256`, and every region base must be below `2 ^ 64`. The
arguments are decoded by `decodeCall`, which does not reduce anything: any other form,
including `OfNat.ofNat` numerals, is rejected.

The decoded arguments are written in the input format of the external runner `vrun`
(`runner/vrun.c` in this repository): registers in the numbering of the Intel SDM
(`rax rcx rdx rbx rsp rbp rsi rdi r8 .. r15`), numbers in hexadecimal without prefix, byte
strings as one token of hexadecimal digit pairs, `-` for an empty one. The runner at the path in
the environment variable `CATCRYPT_VRUN` is started with that text on standard input; exit
status `0` with output `1` accepts the axiom, and anything else rejects it.

## Trusted base

With the flag set, an accepted machine-evaluation claim relies, in addition to the checker, on:

* the recogniser `claim?`, the decoder `decodeCall` and the serialiser `vrunInput` of this
  module;
* the runner executable named by `CATCRYPT_VRUN`, and the agreement of its execution of the code
  with the definition of `machineAcceptsNatD` on the decoded arguments;
* the processor that executes the code.

It does not rely on the Lean compiler that produced the axiom. Every other axiom, including a
`nativeEqTrue` axiom about any other term, is accepted as stated and remains an assumption of
the proofs that use it. The rule only rejects: with the flag set, an accepted axiom is added to
the environment exactly as with the flag off.

## Access to `IO`

The type checker's monad has no `IO`. The single function `runRunner` is an `opaque` constant
whose compiled implementation `runRunnerImpl` runs the runner through `unsafeBaseIO`; to the
logic, and to the `Lean4Lean.Verify` library, `runRunner` is an uninterpreted function.
-/

namespace Lean4Lean.MachineEval
open Lean hiding Environment Exception
open Kernel

/-- The head constant the rule evaluates. -/
def machineAcceptsNatName : Name :=
  `VerifiedEval.machineAcceptsNatD

/-- `Nat`. -/
def natTy : Expr := .const ``Nat []

/-- `List Nat`. -/
def listNatTy : Expr := .app (.const ``List [.zero]) natTy

/-- `Prod Nat (List Nat)`. -/
def regionTy : Expr := .app (.app (.const ``Prod [.zero, .zero]) natTy) listNatTy

/-- A raw natural-number literal. -/
def decodeLit : Expr → Option Nat
  | .lit (.natVal n) => some n
  | _ => none

/-- A closed list `@List.cons.{0} ty x₁ (… (@List.nil.{0} ty))` whose elements `elem` decodes,
appended to `acc`. -/
def decodeList {α : Type} (ty : Expr) (elem : Expr → Option α) :
    Expr → Array α → Option (Array α)
  | .app (.app (.app (.const n ls) t) hd) tl, acc =>
    if n == ``List.cons && ls == [.zero] && t == ty then
      match elem hd with
      | some a => decodeList ty elem tl (acc.push a)
      | none => none
    else none
  | .app (.const n ls) t, acc =>
    if n == ``List.nil && ls == [.zero] && t == ty then some acc else none
  | _, _ => none

/-- A region `@Prod.mk.{0,0} Nat (List Nat) base bytes` with literal base and literal bytes. -/
def decodeRegion : Expr → Option (Nat × Array Nat)
  | .app (.app (.app (.app (.const n ls) a) b) base) bytes =>
    if n == ``Prod.mk && ls == [.zero, .zero] && a == natTy && b == listNatTy then
      match decodeLit base, decodeList natTy decodeLit bytes #[] with
      | some x, some y => some (x, y)
      | _, _ => none
    else none
  | _ => none

/-- The decoded arguments of `machineAcceptsNatD chunks n h regs regions res`. -/
structure Call where
  code : Array Nat
  n : Nat
  regs : Array Nat
  regions : Array (Nat × Array Nat)
  res : Nat

/-- Decode `machineAcceptsNatD chunks n h regs regions res` with literal arguments; `none` on any
other expression. -/
def decodeCall : Expr → Option Call
  | .app (.app (.app (.app (.app (.app (.const f []) code) cnt) _h) regs) regions) res =>
    if f == machineAcceptsNatName then do
      let chunks ← decodeList listNatTy (fun c => decodeList natTy decodeLit c #[]) code #[]
      let code := chunks.foldl (· ++ ·) #[]
      let n ← decodeLit cnt
      let regs ← decodeList natTy decodeLit regs #[]
      let regions ← decodeList regionTy decodeRegion regions #[]
      let res ← decodeLit res
      pure { code, n, regs, regions, res }
    else none
  | _ => none

/-- The range conditions the runner input requires. -/
def Call.validate (c : Call) : Except String Unit := do
  unless c.regs.size == 16 do throw s!"expected 16 registers, got {c.regs.size}"
  unless c.regs.all (fun v => decide (v < 2 ^ 64)) do throw "a register value is not below 2^64"
  unless decide (c.res < 16) do throw s!"result register {c.res} is not below 16"
  unless c.code.all (fun b => decide (b < 256)) do throw "a code byte is not below 256"
  unless c.regions.all (fun r => decide (r.1 < 2 ^ 64) && r.2.all (fun b => decide (b < 256))) do
    throw "a region base is not below 2^64 or a region byte is not below 256"

/-- The lowercase hexadecimal digits of a natural number, without prefix. -/
def hexNat (v : Nat) : String := String.ofList (Nat.toDigits 16 v)

/-- The two lowercase hexadecimal digits of a byte. -/
def hexByte (b : Nat) : String :=
  String.ofList [Nat.digitChar (b / 16 % 16), Nat.digitChar (b % 16)]

/-- A byte string as one token of hexadecimal digit pairs, `-` when empty. -/
def hexBytes (bs : Array Nat) : String :=
  if bs.isEmpty then "-" else bs.foldl (fun s b => s ++ hexByte b) ""

/-- The runner input for a decoded call. -/
def vrunInput (c : Call) : String :=
  let regions := c.regions.foldl (init := "") fun s (base, bs) =>
    s ++ s!"region {hexNat base} {bs.size} {hexBytes bs}\n"
  "VRUN1\n" ++ s!"code {c.code.size} {hexBytes c.code}\n" ++
    "regs " ++ " ".intercalate (c.regs.toList.map hexNat) ++ "\n" ++
    s!"res {c.res}\n" ++ regions ++ "end\n"

/-- Run the runner named by `CATCRYPT_VRUN` on `input` and read its answer. -/
def runnerIO (input : String) : IO Bool := do
  let some path ← IO.getEnv "CATCRYPT_VRUN"
    | throw <| IO.userError "the environment variable CATCRYPT_VRUN is not set"
  let out ← IO.Process.output { cmd := path } (some input)
  if out.exitCode != 0 then
    throw <| IO.userError s!"runner {path} exited with status {out.exitCode}: {out.stderr}"
  if out.stdout == "1\n" then return true
  if out.stdout == "0\n" then return false
  throw <| IO.userError s!"runner {path} printed {repr out.stdout}"

/-- The compiled implementation of `runRunner`: `runnerIO` under `unsafeBaseIO`. -/
unsafe def runRunnerImpl (input : String) : Except String Bool :=
  match unsafeBaseIO (runnerIO input).toBaseIO with
  | .ok b => .ok b
  | .error e => .error (toString e)

/-- The runner's answer on an input. Uninterpreted in the logic; compiled code runs the
external runner through `runRunnerImpl`. -/
@[implemented_by runRunnerImpl]
opaque runRunner (input : String) : Except String Bool

/-- The left side `lhs` of an axiom type `@Eq.{1} Bool lhs Bool.true`. -/
def eqTrueLhs? : Expr → Option Expr
  | .app (.app (.app (.const n ls) ty) lhs) rhs =>
    if n == ``Eq && ls == [levelOne] && ty == .const ``Bool [] &&
        rhs == .const ``Bool.true [] then some lhs else none
  | _ => none

/-- The `machineAcceptsNatD` application that an axiom of type `type` asserts to be `true`: the
left side `lhs` when its head is `machineAcceptsNatD`, or the value of `lhs` when `lhs` is a
constant without universe parameters defined as such an application. `none` otherwise. -/
def claim? (env : Environment) (type : Expr) : Option Expr := do
  let lhs ← eqTrueLhs? type
  if lhs.isAppOf machineAcceptsNatName then return lhs
  let .const c [] := lhs | none
  let some (.defnInfo v) := env.find? c | none
  if v.levelParams.isEmpty && v.value.isAppOf machineAcceptsNatName then some v.value else none

/-- The error of the rule on the axiom `n`. -/
def failOn {α : Type} (n : Name) (msg : String) : Except Exception α :=
  throw <| .other s!"lean4lean machine-eval: rejecting axiom '{n}': {msg}"

/-- Confirm a machine-evaluation claim: succeeds at once when the rule is off or the type of `v`
is not a claim; otherwise succeeds only when the runner answers `true` on the decoded call. -/
def checkAxiom : Bool → Environment → AxiomVal → Except Exception Unit
  | false, _, _ => pure ()
  | true, env, v => do
    let some e := claim? env v.type | pure ()
    let some call := decodeCall e
      | failOn v.name s!"the asserted term is not {machineAcceptsNatName} applied to literal arguments"
    if let .error m := call.validate then failOn v.name m
    match runRunner (vrunInput call) with
    | .ok true => pure ()
    | .ok false => failOn v.name "the machine evaluates the asserted term to false"
    | .error m => failOn v.name m

end Lean4Lean.MachineEval
