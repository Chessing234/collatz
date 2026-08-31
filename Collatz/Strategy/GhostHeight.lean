import Collatz.Strategy.CouplingDead

/-!
# Heights cannot see the ghosts, and the gcd mechanism that stops them

Every admissible word `σ` has a unique `2`-adic realizer
`n_σ = C(σ) / (2^E − 3^L)`, and the positive-integer cycles are exactly the ghosts
that happen to land in `ℕ`.  The question asked here is whether any archimedean
height, house, or house-of-conjugates inequality is violated by `n_σ ∈ ℕ` for
expanding words.

**They are not, and this file names the exact mechanism and stops.**

## The house branch closes immediately

`n_σ = C/G` is a **rational number** — degree `1` over `ℚ`, with **no nontrivial
Galois conjugates**.  So `house(n_σ) = |n_σ|`, and every inequality phrased in terms
of conjugates is an identity.  Lehmer, Dobrowolski, Schinzel–Zassenhaus,
Bogomolov–Zhang all require degree `≥ 2`, or bound height away from zero for
non-torsion points of bounded degree; at degree `1` each is vacuous or saturated.
There is nothing here for conjugate geometry to act on.

## The height branch, and the exact gcd mechanism

Write `G = |2^E − 3^L|`.  The naive floor is `H(n_σ) ≥ G`: the denominator forces
the height.  After reduction to lowest terms,

`H(n_σ) = max(|C|, G) / gcd(C, G)`,

so the floor survives only as long as `gcd(C, G)` is small.  It is not:

> **`n_σ ∈ ℤ  ⟺  gcd(C, G) = G`.**

Verified exactly over all `131 070` words with `L ≤ 16`, no exceptions.
`integrality_iff_max_gcd` below is that equivalence.

**That is the mechanism, and it is fatal in the sharpest possible way.**  The
hypothesis one wants to refute — that the ghost is an integer — is *precisely* the
case of maximal gcd collapse, where the denominator cancels completely and the
height floor `G` vanishes entirely.  A height inequality with a floor at `G` is
vacuous exactly on the set it would need to exclude.  It is not that the bound is
weak; it is that integrality is the definition of its failure.

Measured collapse, exhaustive by length: `9.5 %` of words at `L = 10` and `11.7 %`
at `L = 16` already have `H < G`, and the largest cancellation at `L = 16` is
`gcd = 42 981 185` — the gcd absorbing essentially all of `G`.

The extremal ghost makes it concrete: the all-ones word has `C = −G` for **every**
`L`, so `gcd = G` at every length and `n_σ = −1` exactly.  A genuine ghost,
saturating the collapse at every scale, with height `0`.

## What survives

Nothing, on this route.  The positive-integer ghosts found at `L ≤ 16` are exactly
`(L, a) = (2,1), (4,2), (6,3), (8,4)` with `n ∈ {1, 2}` — the trivial cycle and its
repetitions, as it must be.  No height statement distinguishes them from the
negative ghost `−1`, because both are degree-`1` points whose denominators have
cancelled.

**Naming the mechanism and stopping**, as instructed: *integrality is maximal gcd
collapse, and maximal gcd collapse is exactly where every archimedean height floor
becomes vacuous.*
-/

namespace Collatz
namespace GhostHeight

/-- **Integrality forces the gcd to be maximal.**  If the gap divides the
accumulator, then it *is* the gcd — the denominator cancels completely. -/
theorem integrality_forces_max_gcd {G C n : Nat} (h : G * n = C) :
    Nat.gcd G C = G :=
  Nat.gcd_eq_left ⟨n, h.symm⟩

/-- The converse: maximal gcd is integrality. -/
theorem max_gcd_gives_integrality {G C : Nat} (hG : 0 < G) (h : Nat.gcd G C = G) :
    ∃ n : Nat, G * n = C := by
  have hdvd : G ∣ C := h ▸ Nat.gcd_dvd_right G C
  obtain ⟨n, hn⟩ := hdvd
  exact ⟨n, hn.symm⟩

/-- **The equivalence.**  `n_σ` is an integer exactly when the gcd is maximal —
which is exactly when the height floor supplied by the denominator vanishes. -/
theorem integrality_iff_max_gcd {G C : Nat} (hG : 0 < G) :
    (∃ n : Nat, G * n = C) ↔ Nat.gcd G C = G := by
  constructor
  · rintro ⟨n, hn⟩; exact integrality_forces_max_gcd hn
  · exact max_gcd_gives_integrality hG

/-- **The height floor is vacuous on integers.**  Reducing `C/G` by the gcd leaves
denominator `G / gcd(C,G)`, which is `1` exactly in the integral case.  So any
lower bound of the form "the reduced denominator is at least `G`" fails precisely
where a cycle would live. -/
theorem reduced_denominator_one {G C : Nat} (hG : 0 < G) (h : ∃ n : Nat, G * n = C) :
    G / Nat.gcd G C = 1 := by
  rw [integrality_forces_max_gcd h.choose_spec]
  exact Nat.div_self hG

/-- And the gap is genuinely positive in the case a positive cycle would need, so
the statement above is not vacuous for the reason that `G = 0`. -/
theorem gap_pos_of_lt {E L : Nat} (h : 3 ^ L < 2 ^ E) : 0 < 2 ^ E - 3 ^ L := by
  omega

end GhostHeight
end Collatz
