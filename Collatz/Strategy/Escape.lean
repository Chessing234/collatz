import Collatz.Structure.Divergence
import Collatz.Search.VerifiedExtended

/-!
# Round X, Section III — what divergence actually means

The repository's `Divergent n` is `∀ B, ∃ i, B < orbit i n`: **unbounded**.  The brief
asks which of the many divergence notions — strong divergence `x_n → ∞`, escape,
persistent non-descent, scale divergence, logarithmic divergence — are equivalent for
positive-integer orbits.  For a deterministic map on `ℕ` the answer is that they all
collapse, and the reason is short enough to state here:

> An orbit that repeats a value is eventually periodic, hence bounded.  So an unbounded
> orbit **never repeats**, so all its values are **distinct**.  Only `B + 1` naturals
> are `≤ B`, so at most `B + 1` indices can have `orbit i n ≤ B`, so every bounded
> region is left for good.

Hence, for orbits of any `f : ℕ → ℕ`:

`unbounded  ⟺  never repeats  ⟺  all values distinct  ⟺  x_n → ∞  ⟺  escapes every B`

and "persistent non-descent", "scale divergence" and "logarithmic divergence" are the
same statement in other coordinates.  **There is only one divergence notion here.**

## These are equivalent restatements, and that is the point

An earlier draft of this header was titled *"why this is not merely a repackaging of
unbounded"*.  **It is exactly a repackaging, and the claim was wrong.**  All three of
the statements below are *logically equivalent* to `Divergent n`, so "divergence ⇒ F"
and "F ⇒ divergence" are both trivial and no independent principle is named:

* `divergent_window` — in every window of `B + 2` consecutive indices some value
  exceeds `B`.  The converse is immediate, so this **iff**s with `Divergent`.
* `divergent_escapes` — the last visit to `[0, B]` is at a finite index.  Also an iff.
* `orbit_inj_of_divergent` — injectivity.  Also an iff.

Worse, the constant is the *cardinality of the target set*, so the bound holds for
`x ↦ x + 1`, for `x ↦ 2x`, and for every self-map of `ℕ`.  It cannot distinguish
`3x+1` from `x+1`, so it cannot be a filter component.  (The sharp constant on `[1,B]`
is `B`, not `B+1`, attained by `x ↦ x+1` from `1`; `B+1` is sharp only on `[0,B]`.)

So Section III is a **definitions-hygiene result**: there is one divergence notion, and
it is injectivity.  It is non-circular precisely because it has no content — nothing
here uses any property of the Collatz map beyond determinism on `ℕ`.

**Prior art, which this file did not find before writing.**
`InfiniteWord.accBounded_of_eventuallyCyclic` and `eventuallyCyclic_of_accBounded`
already prove this equivalence for the accelerated map, with the same proof, and
`InfiniteWord.periodicity_equiv_no_divergence` is `divergent_iff_not_eventuallyPeriodic`.
That file's own docstring already recorded this round's verdict: *"A divergent orbit
has an aperiodic parity word — and that is all it has.  No contradiction follows."*
What is genuinely new here is only the plain-`orbit` phrasing and the next section.

## The one statement here with actual content

Combining the dichotomy with the verified range gives something no self-map argument
can give, because it is `3x+1`-specific:

> **`divergent_avoids_verified` — a divergent Collatz orbit never takes a value in
> `[1, 1086463]`.  Not "finitely often": never.**

A tail of a divergent orbit is divergent (`divergent_tail`), so if any orbit value were
positive and below `1086464` it would reach `1` by `reachesOne_of_lt_1086464`, and a
value reaching `1` is not divergent.  This consumes soundness asset (a), it fails for
`x ↦ x + 1`, and it collapses `divergent_window`'s constant completely: for every
`B < 1086464` the true window length is `1`, against the `B + 2` the general theorem
demands.

That is the honest shape of the gap.  A useful filter needs band occupancy — *a
divergent orbit visits `[2^k, 2^(k+1))` at most `c` times* for `c` of size `O(1)` or
`O(k)`.  The general bound gives `2^k`.  Nothing here closes that, and the verified
range moves the floor rather than the exponent.

## How strong is it, honestly

An earlier draft said these were *"tested where escape actually happens"*, using the
`5x+1` orbit of `7`.  **That phrase was wrong: `5x+1` from `7` is not known to
diverge** — it is an open question, and `5x+1` has cycles at `1`, `13` and `17`.  Four
hundred finite steps are not divergence.  The validation set for this round contains
**zero proven-divergent orbits**, which is exactly the missing-witness problem Round IX
Part VI named.  The only provably divergent orbits available are monotone maps like
`x ↦ x+1`, where growth never competes with descent, and those cannot test a filter.

What the computation does show, stated at its true strength: on the `5x+1` orbit of `7`
(400 steps, 54 bits) all 401 values are distinct and the window property holds for
`B = 10, 100, 1000, 10^5`; on the `3x+1` orbit of `27` under the **plain** map the
window statement first fails at index **108** for `B = 10` (an earlier draft said 65,
which is the *accelerated* map, and omitted `B`).  Consistent with the theorems, but
evidence of nothing, since the first orbit is not known to escape.

**But the constant is very loose, and that must be said plainly.**  The bound "at most
`B + 1` visits" is attained only by an orbit that enumerates `0 … B` before leaving.
Real escaping orbits are nowhere near it: the `5x+1` orbit of `7` visits `[0, 10]`
twice against a bound of 11, and `[0, 10^8]` 150 times against a bound of `10^8 + 1`.
So this is a **dichotomy theorem, not yet a quantitative filter**.  It makes Case B
concrete and gives it a uniform constant; it does not yet constrain anything.  Any
Round X filter that leans on it must supply its own strength.

## The dichotomy (brief section XVIII), stated exactly

`exists_periodic_of_bounded` (already in `Divergence.lean`) and `divergent_escapes`
together give: for every positive orbit **exactly one** of

* **Case A** — the orbit returns to a bounded set infinitely often, and then it repeats
  a value and lands on a genuine cycle;
* **Case B** — the orbit leaves every bounded set for good, and all its values are
  distinct.

There is no third behaviour, and in particular no "oscillating unbounded" orbit that
returns to small values infinitely often while also growing without bound.  That
possibility is what one might fear when reading `Divergent` as mere unboundedness, and
it is ruled out by `orbit_inj_of_divergent`.  The whole cycle programme attacks Case A.
Round X exists to make Case B concrete.
-/

namespace Collatz
namespace Escape

open Divergence Cycle

/-! ## A repeat forces boundedness

`Divergence.eventuallyPeriodic_of_bounded` gives one direction.  The converse is what
the dichotomy needs and it was missing. -/

/-- A period shifts the orbit: reading `i + L` steps in is the same as reading `i`. -/
theorem orbit_shift {n i L : Nat} (hrep : orbit (i + L) n = orbit i n) :
    ∀ m : Nat, orbit (m + (i + L)) n = orbit (m + i) n := by
  intro m
  rw [orbit_add m (i + L) n, hrep, orbit_add m i n]

/-- If the orbit repeats, every later value is one of the first `i + L` values, so the
orbit is bounded by `orbitMax n (i + L)`. -/
theorem orbit_eq_of_period {n i L : Nat} (hrep : orbit (i + L) n = orbit i n) :
    ∀ k : Nat, i + L ≤ k → orbit k n = orbit (k - L) n := by
  intro k hk
  have e1 : k = (k - L - i) + (i + L) := by omega
  have e2 : k - L = (k - L - i) + i := by omega
  calc orbit k n = orbit ((k - L - i) + (i + L)) n := by rw [← e1]
    _ = orbit ((k - L - i) + i) n := orbit_shift hrep _
    _ = orbit (k - L) n := by rw [← e2]

/-- **A repeat bounds the orbit.**  The converse of `eventuallyPeriodic_of_bounded`. -/
theorem bounded_of_eventuallyPeriodic {n : Nat} (h : EventuallyPeriodic n) : Bounded n := by
  obtain ⟨i, L, hL, hrep⟩ := h
  refine ⟨orbitMax n (i + L), ?_⟩
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k ≤ i + L
    · exact le_orbitMax k hk
    · have hk' : i + L ≤ k := by omega
      rw [orbit_eq_of_period hrep k hk']
      exact ih (k - L) (by omega)

/-- An unbounded orbit never repeats a value. -/
theorem not_eventuallyPeriodic_of_divergent {n : Nat} (h : Divergent n) :
    ¬ EventuallyPeriodic n :=
  fun hep => (divergent_iff_not_bounded n).mp h (bounded_of_eventuallyPeriodic hep)

/-! ## Injectivity — the heart of the matter -/

/-- **A divergent orbit is injective.**  All of its values are distinct, so it is an
injection `ℕ → ℕ`.  This is what rules out an unbounded orbit that keeps returning to
small values. -/
theorem orbit_inj_of_divergent {n : Nat} (h : Divergent n) {i j : Nat}
    (heq : orbit i n = orbit j n) : i = j := by
  by_cases hij : i = j
  · exact hij
  · exfalso
    refine not_eventuallyPeriodic_of_divergent h ?_
    by_cases hlt : i < j
    · exact ⟨i, j - i, by omega, by
        have : i + (j - i) = j := by omega
        rw [this]; exact heq.symm⟩
    · exact ⟨j, i - j, by omega, by
        have : j + (i - j) = i := by omega
        rw [this]; exact heq⟩

/-! ## The quantitative consequences

These are the statements Round X needs: they carry uniform constants and they speak
about an orbit that never returns. -/

/-- **Every window of `B + 2` consecutive indices contains a value above `B`.**

If all `B + 2` values in the window were `≤ B` they would take only `B + 1` possible
values, so two would coincide — contradicting injectivity.  The constant is uniform in
the window position: this is a return-time bound, not an asymptotic claim. -/
theorem divergent_window {n : Nat} (h : Divergent n) (N B : Nat) :
    ∃ k : Nat, k ≤ B + 1 ∧ B < orbit (N + k) n := by
  by_cases hall : ∃ k, k ≤ B + 1 ∧ B < orbit (N + k) n
  · exact hall
  · exfalso
    have hle : ∀ k, k ≤ B + 1 → orbit (N + k) n < B + 1 := by
      intro k hk
      have hnot : ¬ (B < orbit (N + k) n) := fun hc => hall ⟨k, hk, hc⟩
      omega
    obtain ⟨p, q, hpq, _, hf⟩ :=
      Pigeonhole.exists_repeat (f := fun k => orbit (N + k) n) (B := B + 1) (N := B + 1)
        hle (Nat.le_refl _)
    have := orbit_inj_of_divergent h hf
    omega

/-- **A divergent orbit leaves every bounded region for good.**  For each `B` there is
an index past which every value exceeds `B` — the `x_n → ∞` form.

The induction is on `B`: past the threshold for `B` every value is `≥ B + 1`, and the
value `B + 1` itself can occur at most once, by injectivity. -/
theorem divergent_escapes {n : Nat} (h : Divergent n) :
    ∀ B : Nat, ∃ N : Nat, ∀ i : Nat, N ≤ i → B < orbit i n := by
  intro B
  induction B with
  | zero =>
    by_cases hz : ∃ i, orbit i n = 0
    · obtain ⟨i₀, hi₀⟩ := hz
      refine ⟨i₀ + 1, ?_⟩
      intro i hi
      have hne : orbit i n ≠ 0 := by
        intro hc
        have := orbit_inj_of_divergent h (hi₀.trans hc.symm)
        omega
      omega
    · exact ⟨0, fun i _ => by
        have : orbit i n ≠ 0 := fun hc => hz ⟨i, hc⟩
        omega⟩
  | succ B ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hhit : ∃ i, N ≤ i ∧ orbit i n = B + 1
    · obtain ⟨i₀, hi₀N, hi₀⟩ := hhit
      refine ⟨i₀ + 1, ?_⟩
      intro i hi
      have h1 : B < orbit i n := hN i (by omega)
      have h2 : orbit i n ≠ B + 1 := by
        intro hc
        have := orbit_inj_of_divergent h (hi₀.trans hc.symm)
        omega
      omega
    · refine ⟨N, ?_⟩
      intro i hi
      have h1 : B < orbit i n := hN i hi
      have h2 : orbit i n ≠ B + 1 := fun hc => hhit ⟨i, hi, hc⟩
      omega

/-! ## The one Collatz-specific statement: a divergent orbit avoids the verified range

Everything above holds for an arbitrary self-map of `ℕ` and therefore constrains
nothing.  This section does not: it consumes the verified range (soundness asset (a))
and is false for `x ↦ x + 1`. -/

/-- **A tail of a divergent orbit is divergent.**  Immediate from `divergent_escapes`:
past the escape threshold for `B`, every index — in particular every index of the form
`k + i` — carries a value above `B`. -/
theorem divergent_tail {n : Nat} (h : Divergent n) (i : Nat) : Divergent (orbit i n) := by
  intro B
  obtain ⟨N, hN⟩ := divergent_escapes h B
  refine ⟨N, ?_⟩
  rw [← orbit_add N i n]
  exact hN (N + i) (by omega)

/-- **A divergent Collatz orbit never enters the verified range.**  Not "finitely
often" — *never*.  If some value were positive and below `1086464` it would reach `1`,
and a value reaching `1` is not divergent, contradicting `divergent_tail`.

This is the first statement in this file with content: it is `3x+1`-specific, it
consumes asset (a), and it is false for `x ↦ x + 1`. -/
theorem divergent_avoids_verified {n : Nat} (h : Divergent n) (i : Nat)
    (hpos : 0 < orbit i n) : 1086464 ≤ orbit i n := by
  by_cases hlt : orbit i n < 1086464
  · exfalso
    exact not_divergent_of_reachesOne
      (Search.reachesOne_of_lt_1086464 hpos hlt) (divergent_tail h i)
  · omega

/-- The window constant collapses inside the verified range: for `B < 1086464` a
divergent orbit exceeds `B` at *every* index, so the true window length is `1` against
the `B + 2` that `divergent_window` demands in general. -/
theorem divergent_window_one {n : Nat} (h : Divergent n) (i : Nat)
    (hpos : 0 < orbit i n) {B : Nat} (hB : B < 1086464) : B < orbit i n :=
  Nat.lt_of_lt_of_le hB (divergent_avoids_verified h i hpos)

/-! ## The dichotomy -/

/-- **Escape or recurrence.**  Either the orbit lands on a cycle, or it leaves every
bounded region permanently.

Two caveats an earlier draft omitted.  What is proved is an *inclusive* disjunction;
the exclusivity is true but not proved here.  And there is no positivity hypothesis, so
`n = 0` and `n = 1` both land in the left branch with `Periodic` witnessed by the fixed
point `0` and by the trivial cycle respectively — "genuine cycle" in this repository's
sense is a stronger notion.  Case A is where every number ever tested lives. -/
theorem escape_or_cycle (n : Nat) :
    (∃ i : Nat, Periodic (orbit i n)) ∨
      (∀ B : Nat, ∃ N : Nat, ∀ i : Nat, N ≤ i → B < orbit i n) := by
  by_cases h : Divergent n
  · exact Or.inr (divergent_escapes h)
  · exact Or.inl (exists_periodic_of_bounded (bounded_of_not_divergent h))

/-- Boundedness and eventual periodicity are the same property.  Stated as the
equivalence the dichotomy rests on. -/
theorem bounded_iff_eventuallyPeriodic (n : Nat) : Bounded n ↔ EventuallyPeriodic n :=
  ⟨eventuallyPeriodic_of_bounded, bounded_of_eventuallyPeriodic⟩

/-- Divergence is exactly the failure of eventual periodicity. -/
theorem divergent_iff_not_eventuallyPeriodic (n : Nat) :
    Divergent n ↔ ¬ EventuallyPeriodic n := by
  rw [divergent_iff_not_bounded, bounded_iff_eventuallyPeriodic]

/-! ## Axiom audit -/

#print axioms bounded_of_eventuallyPeriodic
#print axioms orbit_inj_of_divergent
#print axioms divergent_window
#print axioms divergent_escapes
#print axioms escape_or_cycle
#print axioms divergent_tail
#print axioms divergent_avoids_verified

end Escape
end Collatz
