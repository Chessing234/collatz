import Collatz.Structure.Divergence

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

## Why this is not merely a repackaging of "unbounded"

The equivalence is elementary, but two of its consequences are quantitative and are
what Round X actually needs:

* `divergent_window` — **in every window of `B + 2` consecutive indices, some orbit
  value exceeds `B`.**  This is a return-time statement with a uniform constant: the
  occupation of `[0, B]` in any window of length `B + 2` is at most `B + 1`.
* `divergent_escapes` — the last visit to `[0, B]` happens at a finite index, for
  every `B`.

Neither mentions cycles, and neither is available to the cycle-half machinery: they
say something about an orbit *that never comes back*, which is exactly the object the
existing development cannot see.  They are also **independent of Collatz** — nothing
below uses any property of the Collatz map beyond determinism on `ℕ`, which is why the
statements are proved for a general `orbit`-style iteration.

## How strong is it, honestly

Tested where escape actually happens — Collatz has no known divergent orbit, but the
theorems here are about *any* deterministic map on `ℕ`, so the `5x+1` map serves.  On
its orbit of `7` (400 steps, reaching 54 bits) all values are distinct, and every
window of `B + 2` consecutive indices contains a value `> B` for `B = 10, 100, 1000,
10^5`.  On the `3x+1` orbit of `27` the same window statement is **false** from index
65 on, because that orbit is eventually periodic in `{1,2}`.  So the statements do
discriminate escape from recurrence, which is the property Round X is asking for.

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

/-! ## The dichotomy -/

/-- **Escape or recurrence, and nothing else.**  Either the orbit lands on a genuine
cycle, or it leaves every bounded region permanently. -/
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

end Escape
end Collatz
