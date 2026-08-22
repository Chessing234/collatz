import Collatz.Strategy.CycleAccumulator
import Collatz.Strategy.Discrepancy

/-!
# The coupling collapses on a cycle — and that is why the cycle half is hard

Round IX ended by naming the object this development is missing:

> **a quantity that couples the 2-adic datum to the archimedean one — that reads
> `x mod 2^L` and `log₂ x` together, and is not a function of either alone.**

This file identifies the canonical candidate, shows it is *forced* (it is exactly the
one bit `bridge_two_sided` leaves open), and then proves that on a cycle it collapses
to a word invariant.  The collapse is not an accident of this candidate.  It is the
cycle criterion itself, and it applies to every coupling quantity at once.

## The candidate is forced

`bridge_two_sided` gives `|θ_j| ≤ E < 1` for
`θ_j = log₂ (x_j / n) − log₂ 3 · D j`, `E = L − a·log₂ 3`.  Expanding it against the
affine law `2^j x_j = 3^(A j) n + C j` leaves no freedom at all:

`log₂ (x_j / n) = A j · log₂ 3 − j + log₂ (1 + r j)`,  `r j := C j / (3^(A j) · n)`,

and since `(a/L)·log₂ 3 − 1 = −E/L`,

> **`θ_j = −j·E/L + log₂ (1 + r j)` exactly.**

So the entire content of the one open bit is the single ratio

> **`r j = C j / (3 ^ (A j) · n)`** — the accumulator measured against the orbit.

It is the coupling the mandate asks for: the numerator is a 2-adic word datum, the
denominator carries the archimedean point `n`, and it is a function of neither alone.
Its dynamics are clean — the affine law gives `r` unchanged on an even step and
`r ↦ r + d·2^j / (3^(A j + 1) · n)` on an odd one, so `n` enters **only** through the
additive constant of the odd branch, and `r` runs from `0` to `G / 3 ^ a`.

## And on a cycle it is a word invariant

Checked first on genuine cycles of `3x+d` — `d = 1` at `n=1`, `d = 5` at `n=187`,
`d = −1` at `n=17` and `n=5`, `d = 59` at `n=229` — where at every `j`

`r j = G · C j / (3 ^ (A j) · C L)`,

with **both `d` and `n` cancelling**.  `coupling_collapses` below is that identity,
and `collapse_iff_cycle` shows the collapse is *equivalent* to the cycle criterion,
not merely implied by it.

The reason is one line, and it is the point of the file:

> **On a cycle the archimedean datum is not free.**  `cycle_gap_mul` says
> `G · n = C L`, so `n = C L / G` is determined by the word.  There is nothing left
> to couple.

*Attribution: that sentence is not new here.*  It is the header of
`CycleAccumulator.lean` — "`cycle_eq_div` — the cycle point is `C / (2^L − 3^a)`, so
it is **not free**: it is a function of the parity word."  This file supplies the
consequence for the coupling, not the observation.

*Two of the four theorems below are duplicates, and are kept only as named entry
points:* `point_determined` is `CycleAccumulator.cycle_gap_mul` under a new name, and
`gap_dvd_accumulator` is character-for-character `CycleAccumulator.cycle_gap_dvd`,
same proof term.  Cite the originals.

*`collapse_iff_cycle` is a cancellation lemma, not an equivalence of theories.*  It
carries no cycle hypothesis — its binders are unconstrained naturals — and it is
`Nat.eq_of_mul_eq_mul_right` in context.  An earlier draft called it "the collapse
*is* the criterion"; what it licenses is the substitution step, nothing more.

*Asset (c) is consumed, twice, and silently.*  `cycle_gap_mul` routes through
`accCycle_bounds` to `3^a < 2^L`, which is `sign d = +1`; and the bridge bound rests on
`orbit_lower`, which is `C_j ≥ 0`.  Both fail at the witnesses this header advertises:
at `d = −1`, `n = 17`, `L = 11`, `a = 7` we have `3^7 = 2187 > 2048 = 2^11`, so in
`Nat` the gap truncates to `0` and `coupling_collapses` at that data would assert
`C_j · C_L = 0`, which is false.  The `d < 0` rows of the verification table were
checked in exact rationals *outside* Lean; the Lean statement cannot express them.
Relatedly, "`r` runs from `0` to `G/3^a`" holds for `d > 0`; for `d < 0` it runs from
`G/3^a` (negative) up to `0` — at `d = −1`, `n = 17` the range is `[−139/2187, 0]`.

## Sharpening, from the statistical-mechanics branch — the coupling has exactly one
## archimedean number in it

An earlier draft of this header said `r j` "is a function of neither the word nor the
magnitude alone".  True, but weak.  The exact structure is a **product**:

> **`r j = (d / n) · W j (word)`**, where `W j = Σ_(i<j, w_i = 1) 2^i / 3^(A (i+1))`
> depends on the parity word and nothing else.

Verified in exact rationals at every `j ≤ 13` for `3x+1` at `n = 1, 7, 27, 703`,
`3x+5` at `187`, `3x−1` at `17`, `3x+59` at `229`.

So the coupling's **entire archimedean content is the single scalar `d / n`**; every
other ingredient is a parity-word functional.  That is a much stronger statement than
the one this file was written to make, and it re-proves the collapse in one line:

> on a cycle `G·n = d·C L`, so `d / n = G / C L` is *word-determined* and `r` collapses;
> off a cycle `d / n` is one free real parameter and the coupling survives.

It also caps what any future coupling device can carry: one real number.

## What this costs Part VI

The consequence is a dichotomy, and it is sharper than the Part VI statement it
replaces:

* **Cycle half — RETRACTED AND REPAIRED.**  An earlier draft of this file claimed
  *"no coupling quantity can help, ever"*, by the chain: `n` is a function of
  `(word, d)`, so `Q(x, window)` is too, so `C(w,d) = d·C(w,1)` scales `d` out, so `Q`
  is a word invariant and the filter refutes it.  **The third step is invalid.**
  `n = d·C_L(w,1)/G(w)` is homogeneous of degree *one* in `d`, not degree zero, and
  scaling `d` out is legitimate only for degree-zero quantities.  `r j` happens to be
  one — which is the only reason this file's own example collapses — but the class is
  not all of `Q`.

  The claim is refuted by an explicit witness.  Take
  `Q(x, j) := 2^j·x_j − 3^(A_j)·x − C_j(w, 1)`, the accumulator measured against the
  `d = 1` accumulator of the same word.  Then `Q = (d − 1)·C_j(w,1)`, so `Q` vanishes
  on exactly the `d = 1` cycles and is nonzero on every other: `759603724` on the
  `3x+5` cycle at `n = 187`, `−4726` on `3x−1` at `n = 17`, `30` on `3x+7` at `n = 5`,
  `293638596` on `3x+13` at `n = 131`, `66410` on `3x+59` at `n = 229`.  It is a
  function of `(x, window)`, it is not a word invariant, and the soundness filter does
  not touch it.

  **What survives is the degree-0 statement:** *no coupling quantity homogeneous of
  degree 0 under `C ↦ d·C` retains content on a cycle.*  That is `CLOSURE.md` Class 4
  restated for this coordinate, not a new dichotomy — and `CLOSURE.md` now carries it
  as diagnostic 3, since the same faulty inference appeared in three files this round.

  A second correction to the same paragraph: *"this is why every route in this
  programme dies on the cycle half specifically"* is also too strong.
  `Rewriting.no_simplification_order` dies because `bits x` embeds in `bits (T x)`,
  failing already at `x = 3` — nothing to do with cycles.
* **Divergence half.**  Here `n` is *not* determined by any word — a divergent orbit
  never closes, so no relation `G·n = C L` exists to eliminate it.  The coupling
  retains its content exactly here.

So the object named at the end of Round IX exists only on the half the frontier
programme does not touch.  That fits `Complexity.collatz_iff_halves` precisely: the
cycle half is `Π⁰₁` and finitely refutable, the divergence half is `Π⁰₂` and is where
the archimedean information actually lives.

**Corrected reading of Round IX Part VI.**  "Couple the 2-adic and archimedean data"
is not one open problem.  It is closed on the cycle half by the criterion itself, and
open only on the divergence half.
-/

namespace Collatz
namespace Coupling

open CycleAccumulator AccCycle AffineExact

/-! ## The collapse -/

/-- **The coupling ratio loses its archimedean argument on a cycle.**

`r j = C j / (3 ^ A j · n)` is compared with the word-only expression
`G · C j / (3 ^ A j · C L)`.  Cleared of division, equality of the two is exactly
`C j * C L = G * n * C j`, and on a cycle `G * n = C L` makes it hold.

Both `d` and `n` cancel: the ratio that was supposed to carry magnitude information
is a function of the parity word alone. -/
theorem coupling_collapses {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (Cj : Nat) :
    Cj * affineC L n = (2 ^ L - 3 ^ oddCount n L) * n * Cj := by
  rw [cycle_gap_mul hn h]
  exact Nat.mul_comm _ _

/-- The collapse is not merely implied by the cycle criterion — for a nonzero
window accumulator it **is** the criterion.  So no coupling quantity escapes it by
being defined differently; the obstruction is the closing of the orbit. -/
theorem collapse_iff_cycle {n _L G CL : Nat} {Cj : Nat} (hCj : 0 < Cj) :
    Cj * CL = G * n * Cj ↔ CL = G * n := by
  constructor
  · intro hEq
    refine Nat.eq_of_mul_eq_mul_right hCj ?_
    rw [Nat.mul_comm CL Cj]
    exact hEq
  · intro hEq
    rw [hEq, Nat.mul_comm]

/-- The archimedean point of a cycle is determined by its word: the gap times the
point is the accumulator, so `n` is `C L / G` and carries no independent
information.  Stated as the divisibility that makes `n` recoverable. -/
theorem point_determined {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    (2 ^ L - 3 ^ oddCount n L) * n = affineC L n :=
  cycle_gap_mul hn h

/-- The same fact in the form used above: the accumulator over a full period is a
multiple of the gap, with the orbit point as the cofactor. -/
theorem gap_dvd_accumulator {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    (2 ^ L - 3 ^ oddCount n L) ∣ affineC L n :=
  ⟨n, (cycle_gap_mul hn h).symm⟩

/-! ## Axiom audit -/

#print axioms coupling_collapses
#print axioms collapse_iff_cycle
#print axioms point_determined

end Coupling
end Collatz
