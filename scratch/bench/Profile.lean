import Lean4Lean.VerifiedNat
open VerifiedNat

/-- Wall-clock `f` over `iters` iterations, folding results (so no DCE). Every
    `f` must depend on `i` or the optimizer hoists it out of the loop. -/
def timeNs (iters : Nat) (f : Nat → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for i in [0:iters] do
    acc := acc + f i
  let t1 ← IO.monoNanosNow
  return (t1 - t0, acc)

/-- Perturb a limb list at the head by `i` (O(1), forces full recompute). -/
def bump (l : List (BitVec 64)) (i : Nat) : List (BitVec 64) :=
  match l with
  | [] => [BitVec.ofNat 64 i]
  | x :: xs => (x + BitVec.ofNat 64 i) :: xs

def main : IO Unit := do
  let mut sink := 0
  for k in [4, 16, 64, 256] do
    let iters := 4000000 / (k*k) + 5
    let a : Nat := (2 ^ (64*k)) - 3
    let b : Nat := (2 ^ (64*k)) - 5
    let la := ofNat a
    let lb := ofNat b
    let prod := mulDispatch la lb
    -- each phase is i-dependent → not hoistable
    let (tOfNat, s1) ← timeNs iters (fun i => (ofNat (a + i)).length)
    let (tMul,   s2) ← timeNs iters (fun i => (mulDispatch (bump la i) lb).length)
    let (tVal,   s3) ← timeNs iters (fun i => bignumVal (bump prod i) % 1000003)
    let (tRound, s4) ← timeNs iters (fun i => bignumVal (ofNat (a + i)) % 1000003)
    let (tFull,  s5) ← timeNs iters (fun i => verifiedNatMulImpl (a + i) b % 1000003)
    sink := sink + s1 + s2 + s3 + s4 + s5
    let us (n : Nat) : Float := (Float.ofNat (n / iters)) / 1000.0
    IO.println s!"k={k} limbs ({k*64}b), {iters} iters/phase (us/op):"
    IO.println s!"  ofNat(1)={us tOfNat}  mulDispatch={us tMul}  bignumVal(2k)={us tVal}  roundtrip(ofNat+val)={us tRound}  FULL mulImpl={us tFull}"
  IO.println s!"(sink {sink % 97})"
