/-! Prototype + KAT for a computable multi-limb Knuth Algorithm D division over
    little-endian `List (BitVec 64)`. Quotient-digit estimate uses a `128/64`
    hardware division (`BitVec 128` udiv), never a `Nat` big-division. Tested
    against `Nat` div/mod before porting into `VerifiedNat`. -/

def B : Nat := 18446744073709551616  -- 2^64

def valLE : List (BitVec 64) → Nat
  | [] => 0
  | x :: xs => x.toNat + B * valLE xs

def normLE : List (BitVec 64) → List (BitVec 64)
  | [] => []
  | x :: xs => match normLE xs with
    | [] => if x == 0 then [] else [x]
    | r => x :: r

/-- Test-harness only: little-endian limbs of a Nat (uses Nat/%, not in the kernel). -/
partial def toLimbs (n : Nat) : List (BitVec 64) :=
  if n == 0 then [] else BitVec.ofNat 64 (n % B) :: toLimbs (n / B)

/-- Leading zeros of a nonzero 64-bit word. -/
def clzWord (x : BitVec 64) : Nat := 63 - Nat.log2 x.toNat

/-- Shift an array left by `s` bits (`0 ≤ s < 64`); pushes one carry limb. -/
def shlBitsA (a : Array (BitVec 64)) (s : Nat) : Array (BitVec 64) := Id.run do
  if s == 0 then return a.push 0
  let mut out := Array.emptyWithCapacity (a.size + 1)
  let mut carry : BitVec 64 := 0
  for x in a do
    out := out.push ((x <<< s) ||| carry)
    carry := x >>> (64 - s)
  return out.push carry

/-- Shift an array right by `s` bits (`0 ≤ s < 64`). -/
def shrBitsA (a : Array (BitVec 64)) (s : Nat) : Array (BitVec 64) := Id.run do
  if s == 0 then return a
  let n := a.size
  let mut out := Array.replicate n (0 : BitVec 64)
  for i in [0:n] do
    let lo := a[i]! >>> s
    let hi := if i + 1 < n then a[i+1]! <<< (64 - s) else 0
    out := out.set! i (lo ||| hi)
  return out

def b128 : BitVec 128 := (1 : BitVec 128) <<< (64 : Nat)  -- 2^64

/-- Knuth Algorithm D: `(quotient, remainder)` little-endian. -/
def divModD (uL vL : List (BitVec 64)) : List (BitVec 64) × List (BitVec 64) := Id.run do
  let v0 := (normLE vL).toArray
  let u0 := (normLE uL).toArray
  let n := v0.size
  if n == 0 then return ([], [])              -- div by zero: caller excludes
  if u0.size < n then return ([], normLE uL)  -- u < v
  -- n = 1 handled by the single-limb path in VerifiedNat; here support n ≥ 1 anyway
  if n == 1 then
    let d := v0[0]!
    let mut q := Array.replicate u0.size (0 : BitVec 64)
    let mut rem : BitVec 128 := 0
    for jj in [0:u0.size] do
      let i := u0.size - 1 - jj
      let w : BitVec 128 := (rem <<< (64 : Nat)) ||| BitVec.setWidth 128 u0[i]!
      q := q.set! i (BitVec.setWidth 64 (w / BitVec.setWidth 128 d))
      rem := w % BitVec.setWidth 128 d
    return (normLE q.toList, normLE [BitVec.setWidth 64 rem])
  let m := u0.size - n
  let s := clzWord v0[n-1]!
  let v := (shlBitsA v0 s).extract 0 n     -- n limbs, normalized (top bit set)
  let mut u := shlBitsA u0 s               -- m+n+1 limbs (top may be 0)
  -- ensure u has exactly m+n+1 limbs
  while u.size < m + n + 1 do u := u.push 0
  let mut q := Array.replicate (m+1) (0 : BitVec 64)
  let vHi128 : BitVec 128 := BitVec.setWidth 128 v[n-1]!
  let vHi2 : BitVec 64 := v[n-2]!
  for jj in [0:m+1] do
    let j := m - jj
    -- D3: qhat, rhat
    let num128 : BitVec 128 :=
      (BitVec.setWidth 128 u[j+n]! <<< (64 : Nat)) ||| BitVec.setWidth 128 u[j+n-1]!
    let mut qhat : BitVec 128 := num128 / vHi128
    let mut rhat : BitVec 128 := num128 % vHi128
    for _ in [0:2] do
      let cond1 := decide (qhat ≥ b128)
      let lhs : BitVec 128 := qhat * BitVec.setWidth 128 vHi2
      let rhs : BitVec 128 := (rhat <<< (64 : Nat)) ||| BitVec.setWidth 128 u[j+n-2]!
      let cond2 := decide (rhat < b128) && decide (lhs > rhs)
      if cond1 || cond2 then
        qhat := qhat - 1
        rhat := rhat + vHi128
    let qh : BitVec 64 := BitVec.setWidth 64 qhat
    -- D4: multiply-subtract  u[j..j+n] -= qh * v
    let mut carry : BitVec 128 := 0
    let mut borrow : Nat := 0
    for i in [0:n] do
      let p : BitVec 128 := BitVec.setWidth 128 qh * BitVec.setWidth 128 v[i]! + carry
      carry := p >>> (64 : Nat)
      let plo := (BitVec.setWidth 64 p).toNat
      let need := plo + borrow
      let ui := u[j+i]!.toNat
      if ui < need then
        u := u.set! (j+i) (BitVec.ofNat 64 (ui + B - need)); borrow := 1
      else
        u := u.set! (j+i) (BitVec.ofNat 64 (ui - need)); borrow := 0
    -- top limb
    let need := (BitVec.setWidth 64 carry).toNat + borrow
    let ut := u[j+n]!.toNat
    let negBorrow := ut < need
    u := u.set! (j+n) (BitVec.ofNat 64 ((if negBorrow then ut + B else ut) - need))
    -- D5/D6
    if negBorrow then
      q := q.set! j (qh - 1)
      let mut addc : Nat := 0
      for i in [0:n] do
        let sum := u[j+i]!.toNat + v[i]!.toNat + addc
        u := u.set! (j+i) (BitVec.ofNat 64 (sum % B)); addc := if sum ≥ B then 1 else 0
      u := u.set! (j+n) (u[j+n]! + BitVec.ofNat 64 addc)  -- cancels the borrow
    else
      q := q.set! j qh
  -- D8: unnormalize remainder
  let rem := shrBitsA (u.extract 0 n) s
  return (normLE q.toList, normLE rem.toList)

-- deterministic pseudo-random
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % B
def mkN (seed nlimb : Nat) : Nat := Id.run do
  let mut s := seed + 1; let mut acc := 0
  for _ in [0:nlimb] do s := lcg s; acc := acc * B + s
  return acc

def main : IO Unit := do
  let mut fails := 0
  let mut total := 0
  -- random cases across widths
  for un in [2,3,4,6,9,16,32] do
    for vn in [2,3,4,6,9,16] do
      if vn ≤ un then
        for t in [0:60] do
          let u := mkN (t*13 + un*7 + 1) un
          let v := (mkN (t*13 + vn*5 + 3) vn) ||| (1 <<< (64*vn - 1))  -- full width, nonzero
          let (q, r) := divModD (toLimbs u) (toLimbs v)
          let qv := valLE q; let rv := valLE r
          total := total + 1
          unless qv == u / v && rv == u % v do
            fails := fails + 1
            if fails ≤ 5 then IO.println s!"FAIL un={un} vn={vn} t={t}: got q={qv} r={rv}, want q={u/v} r={u%v}"
  -- edge cases: exact division, remainder 0, u=v, u<v, small remainder
  let edge : List (Nat × Nat) :=
    [(mkN 1 6, mkN 2 3), (mkN 3 6 * mkN 4 3, mkN 4 3), (mkN 5 4, mkN 5 4),
     (mkN 6 2, mkN 7 4), (B^4 - 1, B^2), (B^8, B^4 + 7), (mkN 9 9, mkN 10 9)]
  for (u, v) in edge do
    let (q, r) := divModD (toLimbs u) (toLimbs v)
    total := total + 1
    unless valLE q == u / v && valLE r == u % v do
      fails := fails + 1
      IO.println s!"EDGE FAIL u={u} v={v}: got q={valLE q} r={valLE r} want q={u/v} r={u%v}"
  IO.println s!"KAT: {total - fails}/{total} passed ({fails} failed)"
