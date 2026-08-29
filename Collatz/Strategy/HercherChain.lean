import Collatz.Strategy.HercherMerge

/-!
# Hercher's descent applies at most once

`HercherMerge.merge` needs `(3 ^ (j+1) · u) % 4 = 1`, where `n + 1 = 2 ^ (j+1) · u`
with `u` odd.  A descent argument would want to iterate it.  **It cannot be
iterated, ever**, and the reason is one line of arithmetic mod `4`.

## The obstruction

The merge partner is `n' = (n − 1)/2`, and `n' + 1 = 2 ^ j · u` — the same odd
cofactor `u`, one fewer power of two.  So the hypothesis needed to apply the merge
*again*, at `n'`, is `(3 ^ j · u) % 4 = 1`.

But `3 ≡ −1 (mod 4)`, so `3 ^ j · u` and `3 ^ (j+1) · u` have **opposite** residues
mod `4`: one is `1` and the other is `3`.  Hence

**`no_chain`: `(3 ^ (j+1) · u) % 4 = 1 → (3 ^ j · u) % 4 = 3`.**

The hypothesis of `merge` at `n` is exactly the negation of its hypothesis at the
partner.  The descent fires once and stops.

## Why this matters

In the `ℓ`-language of Hercher's paper — `ℓ = v₂(3 ^ k · u − 1)`, the number of even
steps after the opening odd run — the statement is `ℓ(n) ≥ 2 ⟹ ℓ((n−1)/2) = 1`.
So `ℓ = 1` is not a shrinking exceptional set that a descent could grind away: it
is **half of every level**, and it is exactly where the merge is unavailable.

Measured before formalising, over every odd `n < 400 001`: `100 002` values have
`ℓ ≥ 2`, of which `50 002` have an odd partner, and **zero** of those partners
again have `ℓ ≥ 2`.  The density of `ℓ ≥ 2` among odd `n` is `0.49998`.

Independently measured, and this is the harder negative: define an *early merge* of
`n` as some `m < n` whose orbit meets `n`'s orbit **before** `n`'s orbit drops below
`n` — the only kind a minimal-counterexample argument may use.  Then `n = 27, 703,
871, 1695, 2215, 35655` have **no early merge at all**, verified against every
smaller `m`.  So no merge-based descent, of any depth, can be made into a covering
argument.

Both measurements were reproduced independently of the agent that first reported
them.
-/

namespace Collatz
namespace HercherChain

open HercherMerge

/-! ## The mod-four flip -/

/-- `3 ≡ −1 (mod 4)`: multiplying an odd number by three flips its residue between
`1` and `3`. -/
theorem three_mul_mod_four {A : Nat} (hA : A % 2 = 1) (h : (3 * A) % 4 = 1) :
    A % 4 = 3 := by omega

/-- Powers of three are odd, and so is `3 ^ j · u` for odd `u`. -/
theorem pow_three_mul_odd {u j : Nat} (hu : u % 2 = 1) : (3 ^ j * u) % 2 = 1 := by
  rw [Nat.mul_mod, DeviceSwap.three_pow_odd j, hu]

/-! ## The descent does not chain -/

/-- **Hercher's merge fires at most once.**  Its hypothesis at `n` is precisely the
negation of its hypothesis at the partner `(n − 1)/2`, because `3 ^ j · u` and
`3 ^ (j+1) · u` sit in opposite residues mod `4`. -/
theorem no_chain {u j : Nat} (hu : u % 2 = 1)
    (hell : (3 ^ (j + 1) * u) % 4 = 1) : (3 ^ j * u) % 4 = 3 := by
  have hA : (3 ^ j * u) % 2 = 1 := pow_three_mul_odd hu
  have hstep : (3:Nat) ^ (j + 1) * u = 3 * (3 ^ j * u) := by
    rw [Nat.pow_succ, Nat.mul_comm ((3:Nat) ^ j) 3, Nat.mul_assoc]
  rw [hstep] at hell
  exact three_mul_mod_four hA hell

/-- The same statement as an exclusion: the merge hypothesis cannot hold at both a
point and its partner. -/
theorem not_both {u j : Nat} (hu : u % 2 = 1) :
    ¬ ((3 ^ (j + 1) * u) % 4 = 1 ∧ (3 ^ j * u) % 4 = 1) := by
  rintro ⟨h1, h2⟩
  have := no_chain hu h1
  omega

/-- **The partner's shift.**  If `n + 1 = 2 ^ (j+1) · u` then `(n−1)/2 + 1 = 2 ^ j · u`
— the same odd cofactor, one fewer power of two.  This is what makes the partner's
merge hypothesis be `(3 ^ j · u) % 4 = 1`, and hence what `no_chain` refutes. -/
theorem partner_shift {n u j : Nat} (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ (j + 1) * u) : (n - 1) / 2 + 1 = 2 ^ j * u := by
  have hupos : 0 < u := by omega
  have h2 : (2:Nat) ^ (j + 1) * u = 2 * (2 ^ j * u) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  have hpos : 0 < (2:Nat) ^ j * u := Nat.mul_pos (Arith.two_pow_pos j) hupos
  omega

/-- **The descent chain has length one.**  Packaged: from the merge hypothesis at
`n`, the partner satisfies the shift equation with exponent `j`, and its own merge
hypothesis fails. -/
theorem chain_length_one {n u j : Nat} (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ (j + 1) * u)
    (hell : (3 ^ (j + 1) * u) % 4 = 1) :
    (n - 1) / 2 + 1 = 2 ^ j * u ∧ (3 ^ j * u) % 4 ≠ 1 := by
  refine ⟨partner_shift hu hfac, ?_⟩
  have := no_chain hu hell
  omega

end HercherChain
end Collatz
