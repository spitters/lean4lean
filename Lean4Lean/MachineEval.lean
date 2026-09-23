import Lean

/-!
# Machine evaluation of `Lean.reduceBool` on one named function

This module gives the checker one rule for reducing `Lean.reduceBool c`, active only when
`FuelConfig.machineEval` is set (command-line flag `--machine-eval`, or
`--config:machineEval=true`). With the flag off, `reduceNative` throws on every
`Lean.reduceBool c` as before.

The rule applies when the constant `c` is a definition without universe parameters whose value
is, syntactically,

  `CatCrypt.Crypto.SecureCompilation.VerifiedEval.machineAcceptsNat chunks n regs regions res`

where `chunks : List (List Nat)` (the code bytes, in chunks), `regs : List Nat` and
`regions : List (Nat × List Nat)` are closed chains of `List.cons` / `List.nil` / `Prod.mk` (at
universe `0` and at the types `Nat`, `List Nat`, `Prod Nat (List Nat)`) whose leaves are raw
natural-number literals, and `n` (the instruction count) and `res` are raw literals.

The rule returns the processor's answer on the concatenated code bytes. `machineAcceptsNat` is
`false` when the bytes do not decode into exactly `n` instructions, and the rule does not decode
them, so the rule agrees with the definition only on byte strings that decode. That condition is
part of the trusted base: the `verified_decide_lit` tactic emits only bytes whose decoding is
proved, but the rule does not check it.
`regs` must have sixteen entries below `2 ^ 64`, `res` must be below `16`, every byte of the code
and of the regions must be below `256`, and every region base must be below `2 ^ 64`. The
arguments are decoded by `decodeCall`, which does not reduce anything: any other form,
including `OfNat.ofNat` numerals, is rejected and the reduction throws.

The decoded arguments are written in the input format of the external runner `vrun` (source
`CatCrypt/Crypto/SecureCompilation/VerifiedEval/runner/vrun.c` in SSProve-lean): registers in
the numbering of the Intel SDM (`rax rcx rdx rbx rsp rbp rsi rdi r8 .. r15`), numbers in
hexadecimal without prefix, byte strings as one token of hexadecimal digit pairs, `-` for an
empty one. The runner at the path in the environment variable `CATCRYPT_VRUN` is started with
that text on standard input; exit status `0` with output `1` or `0` reduces the application to
`Bool.true` or `Bool.false`, and anything else makes the reduction throw.

## Trusted base

A proof checked with this rule relies, in addition to the checker, on:

* the decoder `decodeCall` and the serialiser `vrunInput` of this module;
* the runner executable named by `CATCRYPT_VRUN`, and the agreement of its execution of the code
  with the definition of `machineAcceptsNat` on the decoded arguments;
* the processor that executes the code.

The rule evaluates the one function `machineAcceptsNat` and no other: `reduceBool` on any other
constant, and every `reduceNat`, still throws.

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
  `CatCrypt.Crypto.SecureCompilation.VerifiedEval.machineAcceptsNat

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

/-- The decoded arguments of `machineAcceptsNat chunks n regs regions res`. -/
structure Call where
  code : Array Nat
  n : Nat
  regs : Array Nat
  regions : Array (Nat × Array Nat)
  res : Nat

/-- Decode `machineAcceptsNat chunks n regs regions res` with literal arguments; `none` on any
other expression. -/
def decodeCall : Expr → Option Call
  | .app (.app (.app (.app (.app (.const f []) code) cnt) regs) regions) res =>
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

/-- The error of the rule on `reduceBool c`. -/
def failOn {α : Type} (c : Name) (msg : String) : Except Exception α :=
  throw <| .other s!"lean4lean machine-eval: cannot reduce 'reduceBool {c}': {msg}"

/-- Reduce `Lean.reduceBool c` by running the runner on the decoded value of `c`. Throws, naming
`c`, when `c` is not a definition whose value `decodeCall` accepts, when the range conditions
fail, or when the runner fails. -/
def reduceBoolConst (env : Environment) (c : Name) : Except Exception Expr := do
  let some (.defnInfo v) := env.find? c | failOn c "not a definition"
  unless v.levelParams.isEmpty do failOn c "the definition has universe parameters"
  let some call := decodeCall v.value
    | failOn c s!"the value is not {machineAcceptsNatName} applied to literal arguments"
  if let .error m := call.validate then failOn c m
  match runRunner (vrunInput call) with
  | .ok true => return .const ``Bool.true []
  | .ok false => return .const ``Bool.false []
  | .error m => failOn c m

end Lean4Lean.MachineEval
