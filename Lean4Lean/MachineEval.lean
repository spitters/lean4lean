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

## Correspondence with `machineAcceptsNatD`

The theorems at the end of this module state what the rule accepts. `claim?_eqTrueE`: every
axiom type `machineAcceptsNatD … = true` is a claim, so no such axiom bypasses the rule.
`checkAxiom_sound`: an accepted claim of either shape is `callE chunks n h regs regions res`,
`machineAcceptsNatD` applied to the literal encodings of the data, with the data within the
ranges of `Call.InRange`, and the runner answers `true` on
`vrunInputLit chunks.flatten regs regions res`. `checkAxiom_callE_iff`: on an axiom of type
`machineAcceptsNatD chunks n h regs regions res = true` with literal data, the rule accepts
exactly when the data is within the ranges and the runner answers `true` on that input.
`vrunInputLit` is, symbol for symbol, the definition of the same name in `VerifiedEval`, whose
compiled implementation of `machineAcceptsNatD` sends this input to the runner; the rule thus
accepts a claim only when the compiled `machineAcceptsNatD` would return `true` on it, and it
rejects in addition the claims whose literals lie outside the ranges.

## Trusted base

With the flag set, an accepted machine-evaluation claim relies, in addition to the checker, on:

* the serialiser `vrunInputLit` of this module (the recogniser `claim?` and the decoder
  `decodeCall` are characterised by the theorems above);
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

/-- `t` is `Nat`. -/
def isNatTy : Expr → Bool
  | .const n [] => n == ``Nat
  | _ => false

/-- `t` is `List.{0} Nat`. -/
def isListNatTy : Expr → Bool
  | .app (.const n [.zero]) t => n == ``List && isNatTy t
  | _ => false

/-- `t` is `Prod.{0,0} Nat (List Nat)`. -/
def isRegionTy : Expr → Bool
  | .app (.app (.const n [.zero, .zero]) a) b => n == ``Prod && isNatTy a && isListNatTy b
  | _ => false

/-- A raw natural-number literal. -/
def decodeLit : Expr → Option Nat
  | .lit (.natVal n) => some n
  | _ => none

/-- A closed list `@List.cons.{0} t x₁ (… (@List.nil.{0} t))` at an element type `t` that `isTy`
accepts, whose elements `elem` decodes, appended to `acc`. -/
def decodeList {α : Type} (isTy : Expr → Bool) (elem : Expr → Option α) :
    Expr → Array α → Option (Array α)
  | .app (.app (.app (.const n [.zero]) t) hd) tl, acc =>
    if n == ``List.cons && isTy t then
      match elem hd with
      | some a => decodeList isTy elem tl (acc.push a)
      | none => none
    else none
  | .app (.const n [.zero]) t, acc =>
    if n == ``List.nil && isTy t then some acc else none
  | _, _ => none

/-- A closed list of raw natural-number literals at type `List Nat`. -/
def decodeNatList (e : Expr) : Option (List Nat) :=
  (decodeList isNatTy decodeLit e #[]).map Array.toList

/-- A region `@Prod.mk.{0,0} Nat (List Nat) base bytes` with literal base and literal bytes. -/
def decodeRegion : Expr → Option (Nat × List Nat)
  | .app (.app (.app (.app (.const n [.zero, .zero]) a) b) base) bytes =>
    if n == ``Prod.mk && isNatTy a && isListNatTy b then
      match decodeLit base, decodeNatList bytes with
      | some x, some y => some (x, y)
      | _, _ => none
    else none
  | _ => none

/-- The decoded arguments of `machineAcceptsNatD chunks n h regs regions res`, with the code
bytes `chunks.flatten`. -/
structure Call where
  code : List Nat
  n : Nat
  regs : List Nat
  regions : List (Nat × List Nat)
  res : Nat

/-- Decode `machineAcceptsNatD chunks n h regs regions res` with literal arguments; `none` on any
other expression. -/
def decodeCall : Expr → Option Call
  | .app (.app (.app (.app (.app (.app (.const f []) code) cnt) _h) regs) regions) res =>
    if f == machineAcceptsNatName then do
      let chunks ← decodeList isListNatTy decodeNatList code #[]
      let n ← decodeLit cnt
      let regs ← decodeNatList regs
      let regions ← decodeList isRegionTy decodeRegion regions #[]
      let res ← decodeLit res
      pure { code := chunks.toList.flatten, n, regs, regions := regions.toList, res }
    else none
  | _ => none

/-- The range conditions the runner input requires. -/
def Call.validate (c : Call) : Except String Unit := do
  unless c.regs.length == 16 do throw s!"expected 16 registers, got {c.regs.length}"
  unless c.regs.all (fun v => decide (v < 2 ^ 64)) do throw "a register value is not below 2^64"
  unless decide (c.res < 16) do throw s!"result register {c.res} is not below 16"
  unless c.code.all (fun b => decide (b < 256)) do throw "a code byte is not below 256"
  unless c.regions.all (fun r => decide (r.1 < 2 ^ 64) && r.2.all (fun b => decide (b < 256))) do
    throw "a region base is not below 2^64 or a region byte is not below 256"

/-- The lowercase hexadecimal digit of `d < 16`. -/
def hexDigit (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- The two hexadecimal digits of a byte value. -/
def hexByte (b : Nat) : String := String.ofList [hexDigit (b / 16 % 16), hexDigit (b % 16)]

/-- The hexadecimal digits of a natural number. -/
def hexNat (v : Nat) : String := String.ofList (Nat.toDigits 16 v)

/-- A byte string as hexadecimal digits, `-` when empty. -/
def hexBytes (bs : List Nat) : String :=
  if bs.isEmpty then "-" else String.join (bs.map hexByte)

/-- The runner input for literal data: the code bytes, the sixteen registers, the result
register number and one `region` line per region. The definition and the four above are, symbol
for symbol, those of the same names in `VerifiedEval` (module `VerifiedEval.VerifiedDecideLit`
and `VerifiedEval.VerifiedDecideHW` of catcrypt-verified-eval), whose `machineAcceptsNatImpl`
sends `vrunInputLit code.flatten regs regions res` to the same runner. -/
def vrunInputLit (code regs : List Nat) (regions : List (Nat × List Nat)) (res : Nat) :
    String :=
  let rs := (List.range 16).map fun k => hexNat (regs.getD k 0 % 2 ^ 64)
  "VRUN1\n" ++ s!"code {code.length} {hexBytes code}\n" ++ "regs " ++ " ".intercalate rs ++
    "\n" ++ s!"res {res}\n" ++
    String.join (regions.map fun p => s!"region {hexNat p.1} {p.2.length} {hexBytes p.2}\n") ++
    "end\n"

/-- The runner input for a decoded call. -/
def vrunInput (c : Call) : String := vrunInputLit c.code c.regs c.regions c.res

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
  | .app (.app (.app (.const n [.succ .zero]) (.const b [])) lhs) (.const t []) =>
    if n == ``Eq && b == ``Bool && t == ``Bool.true then some lhs else none
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

/-! ## The claims the rule accepts -/

/-- The raw literal `n`. -/
def litE (n : Nat) : Expr := .lit (.natVal n)

/-- The list `@List.cons.{0} ty x₁ (… (@List.nil.{0} ty))` of the expressions `xs`. -/
def listE (ty : Expr) : List Expr → Expr
  | [] => .app (.const ``List.nil [.zero]) ty
  | x :: xs => .app (.app (.app (.const ``List.cons [.zero]) ty) x) (listE ty xs)

/-- A list of natural numbers as raw literals. -/
def natListE (l : List Nat) : Expr := listE natTy (l.map litE)

/-- Chunks of natural numbers as raw literals. -/
def chunksE (cs : List (List Nat)) : Expr := listE listNatTy (cs.map natListE)

/-- A region `(base, bytes)` as raw literals. -/
def regionE (r : Nat × List Nat) : Expr :=
  .app (.app (.app (.app (.const ``Prod.mk [.zero, .zero]) natTy) listNatTy) (litE r.1))
    (natListE r.2)

/-- A list of regions as raw literals. -/
def regionsE (rs : List (Nat × List Nat)) : Expr := listE regionTy (rs.map regionE)

/-- `machineAcceptsNatD chunks n h regs regions res` with literal data and the proof term `h`. -/
def callE (chunks : List (List Nat)) (n : Nat) (h : Expr) (regs : List Nat)
    (regions : List (Nat × List Nat)) (res : Nat) : Expr :=
  .app (.app (.app (.app (.app (.app (.const machineAcceptsNatName []) (chunksE chunks))
    (litE n)) h) (natListE regs)) (regionsE regions)) (litE res)

/-- `@Eq.{1} Bool lhs Bool.true`. -/
def eqTrueE (lhs : Expr) : Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) lhs) (.const ``Bool.true [])

/-- The range conditions of `Call.validate` as a proposition. -/
def Call.InRange (c : Call) : Prop :=
  c.regs.length = 16 ∧ (∀ v ∈ c.regs, v < 2 ^ 64) ∧ c.res < 16 ∧ (∀ b ∈ c.code, b < 256) ∧
    ∀ r ∈ c.regions, r.1 < 2 ^ 64 ∧ ∀ b ∈ r.2, b < 256

/-- `isNatTy` recognises `natTy` only. -/
theorem isNatTy_iff (t : Expr) : isNatTy t = true ↔ t = natTy := by
  unfold isNatTy; split <;> grind [natTy]

/-- `isListNatTy` recognises `listNatTy` only. -/
theorem isListNatTy_iff (t : Expr) : isListNatTy t = true ↔ t = listNatTy := by
  unfold isListNatTy; split <;> grind [listNatTy, isNatTy_iff]

/-- `isRegionTy` recognises `regionTy` only. -/
theorem isRegionTy_iff (t : Expr) : isRegionTy t = true ↔ t = regionTy := by
  unfold isRegionTy; split <;> grind [regionTy, isNatTy_iff, isListNatTy_iff]

/-- `decodeLit` decodes exactly the raw literals. -/
theorem decodeLit_eq_some_iff (e : Expr) (a : Nat) : decodeLit e = some a ↔ e = litE a := by
  unfold decodeLit; split <;> grind [litE]

/-- `decodeList` decodes the list expression of encoded elements. -/
theorem decodeList_listE {α : Type} {isTy : Expr → Bool} {ty : Expr} {elem : Expr → Option α}
    {g : α → Expr} (hty : isTy ty = true) (hel : ∀ a, elem (g a) = some a) (as : List α)
    (acc : Array α) :
    decodeList isTy elem (listE ty (as.map g)) acc = some (acc ++ as.toArray) := by
  induction as generalizing acc with
  | nil => simp [listE, decodeList, hty]
  | cons a as ih => simp [listE, decodeList, hty, hel, ih]

/-- An expression that `decodeList` decodes is the list expression of encoded elements. -/
theorem decodeList_eq_some {α : Type} {isTy : Expr → Bool} {ty : Expr} {elem : Expr → Option α}
    {g : α → Expr} (hty : ∀ t, isTy t = true → t = ty) (hel : ∀ e a, elem e = some a → e = g a)
    (e : Expr) (acc r : Array α) (h : decodeList isTy elem e acc = some r) :
    ∃ as : List α, r = acc ++ as.toArray ∧ e = listE ty (as.map g) := by
  fun_induction decodeList isTy elem e acc generalizing r with
  | case1 n t hd tl acc hc a ha ih =>
    obtain ⟨as, rfl, rfl⟩ := ih r h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, ht⟩ := hc
    exact ⟨a :: as, by simp, by simp [listE, hty t ht, hel hd a ha]⟩
  | case4 n t acc hc =>
    simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hc h
    obtain ⟨rfl, ht⟩ := hc
    exact ⟨[], by simp [h], by simp [listE, hty t ht]⟩
  | _ => simp at h

/-- `decodeNatList` decodes exactly the literal lists `natListE l`. -/
theorem decodeNatList_eq_some_iff (e : Expr) (l : List Nat) :
    decodeNatList e = some l ↔ e = natListE l := by
  constructor
  · intro h
    simp only [decodeNatList, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    obtain ⟨as, rfl, rfl⟩ := decodeList_eq_some (ty := natTy) (g := litE)
      (fun t ht => (isNatTy_iff t).1 ht) (fun e a h => (decodeLit_eq_some_iff e a).1 h) e #[] r hr
    simp [natListE]
  · rintro rfl
    simp [decodeNatList, natListE,
      decodeList_listE ((isNatTy_iff natTy).2 rfl) (fun a => (decodeLit_eq_some_iff _ a).2 rfl)]

/-- `decodeRegion` decodes exactly the literal regions `regionE r`. -/
theorem decodeRegion_eq_some_iff (e : Expr) (r : Nat × List Nat) :
    decodeRegion e = some r ↔ e = regionE r := by
  unfold decodeRegion
  split
  next n a b base bytes =>
    constructor
    · intro h
      split at h
      next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨rfl, ha⟩, hb⟩ := hc
        split at h
        next x y hx hy =>
          cases h
          rw [decodeLit_eq_some_iff] at hx
          rw [decodeNatList_eq_some_iff] at hy
          simp [regionE, (isNatTy_iff a).1 ha, (isListNatTy_iff b).1 hb, hx, hy]
        next => simp at h
      next => simp at h
    · intro h
      simp only [regionE, Expr.app.injEq, Expr.const.injEq] at h
      obtain ⟨⟨⟨⟨⟨rfl, -⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
      have hy := (decodeNatList_eq_some_iff (natListE r.2) r.2).2 rfl
      simp [isNatTy_iff, isListNatTy_iff, decodeLit, litE, hy]
  next hne =>
    simp only [reduceCtorEq, false_iff]
    intro h
    exact hne _ _ _ _ _ (h.trans rfl)

/-- `decodeCall` decodes every application `callE` of literal data. -/
theorem decodeCall_callE (chunks : List (List Nat)) (n : Nat) (h : Expr) (regs : List Nat)
    (regions : List (Nat × List Nat)) (res : Nat) :
    decodeCall (callE chunks n h regs regions res) =
      some { code := chunks.flatten, n, regs, regions, res } := by
  have h1 : decodeList isListNatTy decodeNatList (listE listNatTy (chunks.map natListE)) #[] =
      some chunks.toArray := by
    simpa using decodeList_listE ((isListNatTy_iff _).2 rfl)
      (fun a => (decodeNatList_eq_some_iff _ a).2 rfl) chunks #[]
  have h2 : decodeList isRegionTy decodeRegion (listE regionTy (regions.map regionE)) #[] =
      some regions.toArray := by
    simpa using decodeList_listE ((isRegionTy_iff _).2 rfl)
      (fun a => (decodeRegion_eq_some_iff _ a).2 rfl) regions #[]
  have h3 := (decodeNatList_eq_some_iff (natListE regs) regs).2 rfl
  simp [callE, decodeCall, chunksE, regionsE, h1, h2, h3, decodeLit, litE]

/-- An expression that `decodeCall` decodes is an application `callE` of literal data. -/
theorem decodeCall_eq_some (e : Expr) (c : Call) (hc : decodeCall e = some c) :
    ∃ chunks n h regs regions res, e = callE chunks n h regs regions res ∧
      c = { code := chunks.flatten, n, regs, regions, res } := by
  unfold decodeCall at hc
  split at hc
  next f code cnt h regs regions res =>
    split at hc
    next hf =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
      obtain ⟨chs, hch, n, hn, rs, hrs, rgs, hrgs, r, hr, rfl⟩ := hc
      obtain ⟨cs, rfl, rfl⟩ := decodeList_eq_some (ty := listNatTy) (g := natListE)
        (fun t ht => (isListNatTy_iff t).1 ht) (fun e a h => (decodeNatList_eq_some_iff e a).1 h)
        _ _ _ hch
      obtain ⟨gs, rfl, rfl⟩ := decodeList_eq_some (ty := regionTy) (g := regionE)
        (fun t ht => (isRegionTy_iff t).1 ht) (fun e a h => (decodeRegion_eq_some_iff e a).1 h)
        _ _ _ hrgs
      rw [decodeLit_eq_some_iff] at hn hr
      rw [decodeNatList_eq_some_iff] at hrs
      subst hn hr hrs
      simp only [beq_iff_eq] at hf
      subst hf
      exact ⟨cs, n, h, rs, gs, r, rfl, by simp⟩
    next => simp at hc
  next => simp at hc

/-- `Call.validate` succeeds exactly on the calls within the ranges. -/
theorem Call.validate_eq_ok_iff (c : Call) : c.validate = .ok () ↔ c.InRange := by
  simp only [Call.validate, Call.InRange]
  repeat' split
  all_goals simp_all [throw, throwThe, MonadExceptOf.throw, Except.bind, bind, pure, Except.pure]
  all_goals grind

/-- The head of `callE` is `machineAcceptsNatD`. -/
theorem callE_isAppOf (chunks : List (List Nat)) (n : Nat) (h : Expr) (regs : List Nat)
    (regions : List (Nat × List Nat)) (res : Nat) :
    (callE chunks n h regs regions res).isAppOf machineAcceptsNatName = true := by
  simp [callE, Expr.isAppOf, Expr.getAppFn]

/-- Every axiom type `machineAcceptsNatD … = true` is a claim of the rule. -/
theorem claim?_eqTrueE (env : Environment) (lhs : Expr)
    (h : lhs.isAppOf machineAcceptsNatName = true) : claim? env (eqTrueE lhs) = some lhs := by
  simp [claim?, eqTrueE, eqTrueLhs?, h]

/-- An axiom whose type is not a claim is accepted as upstream accepts it. -/
theorem checkAxiom_of_claim?_eq_none (env : Environment) (v : AxiomVal)
    (h : claim? env v.type = none) : checkAxiom true env v = .ok () := by
  simp only [checkAxiom, h]
  rfl

/-- With the rule on, a claim `e` is accepted exactly when it decodes to a call within the
ranges on which the runner answers `true`. -/
theorem checkAxiom_eq_ok_iff_of_claim? (env : Environment) (v : AxiomVal) (e : Expr)
    (h : claim? env v.type = some e) :
    checkAxiom true env v = .ok () ↔
      ∃ c, decodeCall e = some c ∧ c.InRange ∧ runRunner (vrunInput c) = .ok true := by
  simp only [checkAxiom, h]
  rcases hd : decodeCall e with _ | c
  · simp [failOn, throw, throwThe, MonadExceptOf.throw]
  · have hiff := Call.validate_eq_ok_iff c
    simp only [Option.some.injEq, exists_eq_left']
    rcases hv : c.validate with m | ⟨⟩ <;> rcases hr : runRunner (vrunInput c) with m' | b
    all_goals (try cases b) <;>
      simp_all [failOn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]

/-- Soundness of the rule for both shapes of claim: an accepted claim is
`machineAcceptsNatD chunks n h regs regions res` with literal data within the ranges, and the
runner answers `true` on `vrunInputLit chunks.flatten regs regions res`. -/
theorem checkAxiom_sound (env : Environment) (v : AxiomVal) (e : Expr)
    (hc : claim? env v.type = some e) (h : checkAxiom true env v = .ok ()) :
    ∃ chunks n p regs regions res, e = callE chunks n p regs regions res ∧
      Call.InRange { code := chunks.flatten, n, regs, regions, res } ∧
      runRunner (vrunInputLit chunks.flatten regs regions res) = .ok true := by
  obtain ⟨c, hd, hr, hrun⟩ := (checkAxiom_eq_ok_iff_of_claim? env v e hc).1 h
  obtain ⟨chunks, n, p, regs, regions, res, rfl, rfl⟩ := decodeCall_eq_some e c hd
  exact ⟨chunks, n, p, regs, regions, res, rfl, hr, hrun⟩

/-- The rule on an axiom asserting `machineAcceptsNatD chunks n h regs regions res = true` with
literal data: it accepts exactly when the data is within the ranges and the runner answers
`true` on `vrunInputLit chunks.flatten regs regions res`, the input that the compiled
implementation of `machineAcceptsNatD` sends to the runner. -/
theorem checkAxiom_callE_iff (env : Environment) (v : AxiomVal) (chunks : List (List Nat))
    (n : Nat) (p : Expr) (regs : List Nat) (regions : List (Nat × List Nat)) (res : Nat)
    (hv : v.type = eqTrueE (callE chunks n p regs regions res)) :
    checkAxiom true env v = .ok () ↔
      Call.InRange { code := chunks.flatten, n, regs, regions, res } ∧
      runRunner (vrunInputLit chunks.flatten regs regions res) = .ok true := by
  rw [checkAxiom_eq_ok_iff_of_claim? env v _
    (hv ▸ claim?_eqTrueE env _ (callE_isAppOf chunks n p regs regions res)), decodeCall_callE]
  simp [vrunInput]

end Lean4Lean.MachineEval
