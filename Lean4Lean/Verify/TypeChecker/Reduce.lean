import Lean4Lean.Verify.TypeChecker.Basic
import Lean4Lean.VerifiedNatArrayProofs

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem rawNatLitExt?.WF {c : VContext} (H : rawNatLitExt? e = some n) (he : c.TrExprS e e') :
    c.venv.contains ``Nat ∧ e' = .natLit n := by
  have : c.TrExprS (.lit (.natVal n)) e' := by
    unfold rawNatLitExt? at H; split at H <;> rename_i h
    · cases H; have := he.eqv h; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · unfold Expr.rawNatLit? at H; split at H <;> cases H; exact he
  have hn := this.lit_has_type
  exact ⟨hn, this.unique (by trivial) (TrExprS.natLit c.hasPrimitives hn n).1⟩

theorem natLimbsInsert.WF {c : VContext} {s : VState} {k : NatKey} {a : NatLimbs k} :
    M.WF c s (natLimbsInsert k a) fun _ _ => True := by
  rintro wf _ _ ⟨⟩
  exact ⟨{ s with toState := _ }, rfl, .rfl, { wf with }, trivial⟩

theorem natLimbsGet.WF {c : VContext} {s : VState} {n : Nat} :
    M.WF c s (natLimbsGet n) fun _ _ => True := by
  unfold natLimbsGet
  refine M.WF.bind get.WF fun _ _ _ _ => ?_
  split
  · exact .pure trivial
  · exact natLimbsInsert.WF.bind fun _ _ _ _ => .pure trivial

theorem natLimbsResult.WF {c : VContext} {s : VState} {r : Array UInt64} :
    M.WF c s (natLimbsResult r) fun v _ => v = VerifiedNat.toNatA r := by
  unfold natLimbsResult
  refine natLimbsInsert.WF.bind fun _ _ _ _ => .pure ?_
  show VerifiedNat.toNatA (VerifiedNat.normA r) = _
  rw [VerifiedNat.normA_eq_ofNatA, VerifiedNat.toNatA_ofNatA]

theorem natPureOp.WF {c : VContext} {s : VState} {f : Nat → Nat → Nat} :
    M.WF c s (natPureOp f v1 v2) fun v _ => v = f v1 v2 := .pure rfl

theorem natBinOpLimbs.WF {c : VContext} {s : VState} {f g}
    (hg : ∀ x y, VerifiedNat.toNatA (g (VerifiedNat.ofNatA x) (VerifiedNat.ofNatA y)) = f x y) :
    M.WF c s (natBinOpLimbs f g v1 v2) fun v _ => v = f v1 v2 := by
  unfold natBinOpLimbs
  split
  · exact .pure rfl
  · refine natLimbsGet.WF.bind fun x1 _ _ _ => natLimbsGet.WF.bind fun x2 _ _ _ => ?_
    refine natLimbsResult.WF.le fun _ _ _ h => ?_
    rw [h, x1.2, x2.2, hg]

theorem natShiftOpLimbs.WF {c : VContext} {s : VState} {f g}
    (hg : ∀ x k, VerifiedNat.toNatA (g (VerifiedNat.ofNatA x) k) = f x k) :
    M.WF c s (natShiftOpLimbs f g v1 v2) fun v _ => v = f v1 v2 := by
  unfold natShiftOpLimbs
  split
  · exact .pure rfl
  · refine natLimbsGet.WF.bind fun x1 _ _ _ => ?_
    refine natLimbsResult.WF.le fun _ _ _ h => ?_
    rw [h, x1.2, hg]

theorem natPowLimbs.WF {c : VContext} {s : VState} :
    M.WF c s (natPowLimbs v1 v2) fun v _ => v = Nat.pow v1 v2 := by
  unfold natPowLimbs
  split
  · exact .pure rfl
  · refine natLimbsGet.WF.bind fun x1 _ _ _ => ?_
    refine natLimbsResult.WF.le fun _ _ _ h => ?_
    rw [h, x1.2, VerifiedNat.toNatA_powA_ofNatA]; rfl

theorem natBinPredLimbs.WF {c : VContext} {s : VState} {f g}
    (hg : ∀ x y, g (VerifiedNat.ofNatA x) (VerifiedNat.ofNatA y) = f x y) :
    M.WF c s (natBinPredLimbs f g v1 v2) fun v _ => v = f v1 v2 := by
  unfold natBinPredLimbs
  split
  · exact .pure rfl
  · refine natLimbsGet.WF.bind fun x1 _ _ _ => natLimbsGet.WF.bind fun x2 _ _ _ => .pure ?_
    rw [x1.2, x2.2, hg]

def reduceBinNatOpG (guard : Nat → Nat → Prop) [DecidableRel guard]
    (op : Nat → Nat → M Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  if guard v1 v2 then return none
  return some <| .lit <| .natVal <| ← op v1 v2

theorem reduceBinNatOpG.WF {guard} [DecidableRel guard] {c : VContext} {op : Nat → Nat → M Nat}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc f)
    (hop : ∀ v1 v2 (s : VState), M.WF c s (op v1 v2) fun r _ => r = f v1 v2) :
    RecM.WF c s (reduceBinNatOpG guard op a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatOpG
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]
  obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]
  cases (rawNatLitExt?.WF h b2).2
  split <;> [exact .pure nofun; rename_i h]
  refine (hop v1 v2 _).lift.bind fun r _ _ hr => .pure ?_
  subst hr
  rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  refine ⟨_, (TrExprS.natLit c.hasPrimitives hn _).1, ?_⟩
  have := (heval ⟨_, h1⟩).2 v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact ⟨_, .appDF this b3⟩

theorem reduceBinNatPred.WF {c : VContext} {op : Nat → Nat → M Bool}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatBool fc f)
    (hop : ∀ v1 v2 (s : VState), M.WF c s (op v1 v2) fun r _ => r = f v1 v2) :
    RecM.WF c s (reduceBinNatPred op a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatPred
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]; cases (rawNatLitExt?.WF h a2).2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]; cases (rawNatLitExt?.WF h b2).2
  refine (hop v1 v2 _).lift.bind fun r _ _ hr => .pure ?_
  subst hr
  rintro _ ⟨⟩; refine ⟨fun _ _ _ => .boolLit, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  have := (heval ⟨_, h1⟩).2 v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine ⟨_, (TrExprS.boolLit c.hasPrimitives ?_ _).1, ?_⟩
  · let ⟨_, H⟩ := this
    exact VExpr.WF.boolLit_has_type c.Ewf c.hasPrimitives (Γ := []) trivial ⟨_, H.hasType.2⟩
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact  ⟨_, .appDF this b3⟩

theorem reduceNat.WF {c : VContext} (he : c.TrExprS e e') :
    RecM.WF c s (reduceNat e) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  generalize hP : (fun oe => _) = P
  refine let prims := _; have hprims : Environment.primitives = .ofList prims := rfl; ?_
  replace hprims {a} : Environment.primitives.contains a ↔ a ∈ prims := by
    simp [hprims, NameSet.contains, NameSet.ofList]
  unfold reduceNat; extract_lets nargs F1 fn
  cases h1 : nargs == 1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases nargs == 2 <;> [exact hP ▸ .pure nofun; simp only [↓reduceIte]]
    split <;> [rename_i f ls a b; exact hP ▸ .pure nofun]
    have hfun guard {g fc G op} [DecidableRel guard] (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatNat fc g)
        (hop : ∀ v1 v2 (s : VState), M.WF c s (op v1 v2) fun r _ => r = g v1 v2)
        (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatOpG guard op a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatOpG.WF he (hprims.2 hprim) heval hop
    have hpred {g fc G op} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatBool fc g)
        (hop : ∀ v1 v2 (s : VState), M.WF c s (op v1 v2) fun r _ => r = g v1 v2)
        (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatPred op a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatPred.WF he (hprims.2 hprim) heval hop
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natAdd
      fun _ _ _ => natBinOpLimbs.WF VerifiedNat.toNatA_addA_ofNatA
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natSub
      fun _ _ _ => natBinOpLimbs.WF VerifiedNat.toNatA_subA_ofNatA
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMul
      fun _ _ _ => natBinOpLimbs.WF VerifiedNat.toNatA_mulA_ofNatA
    apply hfun _ (by simp [prims]) c.hasPrimitives.natPow fun _ _ _ => natPowLimbs.WF
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natGcd
      fun _ _ _ => natPureOp.WF
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMod
      fun _ _ _ => natPureOp.WF
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natDiv
      fun _ _ _ => natPureOp.WF
    apply hpred (by simp [prims]) c.hasPrimitives.natBEq
      fun _ _ _ => natBinPredLimbs.WF VerifiedNat.beqA_ofNatA
    apply hpred (by simp [prims]) c.hasPrimitives.natBLE
      fun _ _ _ => natBinPredLimbs.WF VerifiedNat.bleA_ofNatA
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLAnd
      fun _ _ _ => natBinOpLimbs.WF VerifiedNat.toNatA_landA_ofNatA
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLOr
      fun _ _ _ => natBinOpLimbs.WF VerifiedNat.toNatA_lorA_ofNatA
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natXor
      fun _ _ _ => natBinOpLimbs.WF VerifiedNat.toNatA_xorA_ofNatA
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftLeft
      fun _ _ _ => natShiftOpLimbs.WF VerifiedNat.toNatA_shiftLeftA_ofNatA
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftRight
      fun _ _ _ => natShiftOpLimbs.WF VerifiedNat.toNatA_shiftRightA_ofNatA
    exact hP ▸ .pure nofun
  · split <;> [rename_i h2; exact hP ▸ .pure nofun]
    simp [nargs, Expr.getAppNumArgs_eq] at h1; subst fn
    let .app f a := e; simp [Expr.appFn!, Expr.eqv_const] at h2 ⊢; subst h2
    let .app ha1 ha2 hf ha := he
    let .const h1 h2 h3 := hf
    refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
    split <;> [rename_i n h; exact hP ▸ .pure nofun]
    obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
    refine hP ▸ .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
    have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
    have ⟨c2, c3⟩ := c.safePrimitives c1 <| hprims.2 (by simp [prims])
    have ⟨d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1; cases h2
    refine have ⟨p1, p2⟩ := TrExprS.natLit c.hasPrimitives hn _; ⟨_, p1, ?_⟩
    refine p2.toU.symm.trans c.Ewf c.Δwf ?_
    exact ⟨_, ha1.appDF <| a3.of_r c.Ewf c.Δwf ha2⟩

theorem reduceProjCore.WF (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProjCore i e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := sorry

theorem reduceProj.WF (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProj i e cheapProj) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceProj
  have .proj (e' := s) a1 a2 := he
  refine .bind (Q := fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ s) ?_ fun _ _ _ ⟨h1, h2⟩ => ?_
  · split <;> [exact whnfCore.WF a1; exact whnf.WF a1]
  have ⟨_, b1, b2⟩ := h2.proj c.Ewf c.Δwf a2
  refine (reduceProjCore.WF b1).mono fun _ _ _ H _ eq => ?_
  have ⟨c1, c2⟩ := H _ eq; exact ⟨h1.trans c1, c2.defeq c.Ewf c.Δwf b2⟩
