/-- Generate modmul certificates `(A*B) % P = C := rfl` at crypto-prime widths.
    This is the per-step shape of a kernel-checked primality/modexp certificate:
    a full-width multiply followed by a reduction modulo an n-limb modulus. -/
def two64 : Nat := 18446744073709551616

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % two64

/-- An `nlimb`-limb number from a seed (top bit set so it is exactly full width). -/
def mkNum (seed nlimb : Nat) : Nat := Id.run do
  let mut s := seed + 1
  let mut acc := 0
  for _ in [0:nlimb] do
    s := lcg s
    acc := acc * two64 + s
  return acc ||| (1 <<< (64 * nlimb - 1))

def main : IO Unit := do
  -- (bits, limbs, lemma-count): big counts dilute out the ~0.3s load+replay floor
  let widths : List (Nat × Nat × Nat) :=
    [(384, 6, 3000), (576, 9, 2000), (2048, 32, 800)]
  for (bits, nlimb, n) in widths do
    let mut out := "set_option maxRecDepth 1000000\n"
    for i in [0:n] do
      let a := mkNum (i * 7 + 1) nlimb
      let b := mkNum (i * 7 + 3) nlimb
      let p := (mkNum (i * 7 + 5) nlimb) ||| 1   -- odd modulus
      let c := (a * b) % p
      out := out ++ s!"theorem t{i} : ({a} * {b}) % {p} = {c} := rfl\n"
    IO.FS.writeFile s!"scratch/bench/MulModW{bits}.lean" out
    IO.println s!"wrote MulModW{bits}.lean ({n} lemmas, {nlimb} limbs)"
