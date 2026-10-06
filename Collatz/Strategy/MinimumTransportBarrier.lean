import Collatz.Strategy.DescentRounds

/-!
# Density transport stops at the orbit minimum

Every fixed first-descent iterate preserves density one. Its pointwise
stabilized endpoint does not: it sends every input into the density-zero
set of starts with no finite stopping time. Any time rule reaching such
endpoints on a density-one set has density-one tails beyond every fixed
horizon, and hence is not density-tight.
-/
namespace Collatz.MinimumTransportBarrier
open NaturalDensity StepDensityTransport StoppingRuleDensity DescentRounds

/-- The orbit-minimum map sends every start outside finite stopping time. -/
theorem minimum_no_drop (n : Nat) : ¬hasFiniteStoppingTime (orbitMinimum n) :=
  diagonal_no_drop n

/-- A concrete density-one predicate whose preimage under orbitMinimum is empty. -/
theorem minimum_destroys_density :
    DensityOne hasFiniteStoppingTime ∧
    ¬DensityOne (fun n => hasFiniteStoppingTime (orbitMinimum n)) := by
  refine ⟨StoppingNaturalDensity.finite_stopping_time_density_one, ?_⟩
  intro h
  exact not_densityOne_empty (densityOne_mono (fun n hn => minimum_no_drop n hn) h)

/-- Thus preservation by all finite rounds does not pass to their pointwise
stabilized endpoint. This is about the actual Collatz map. -/
theorem no_minimum_transport :
    ¬(∀ P : Nat → Prop, DensityOne P → DensityOne (fun n => P (orbitMinimum n))) := by
  intro h
  exact minimum_destroys_density.2 (h _ minimum_destroys_density.1)

/-- Every non-descending start is already its own orbit minimum. -/
theorem minimum_eq_self_of_no_drop {n : Nat} (h : ¬hasFiniteStoppingTime n) :
    orbitMinimum n=n :=
  rounds_fixed (descentMap_eq_of_no_drop h) n

/-- The range of the minimum map is exactly the non-descending set, rather
than just a subset of it. -/
theorem minimum_image_iff (m : Nat) :
    (∃ n, orbitMinimum n=m) ↔ ¬hasFiniteStoppingTime m := by
  constructor
  · rintro ⟨n, rfl⟩
    exact minimum_no_drop n
  · intro h
    exact ⟨m, minimum_eq_self_of_no_drop h⟩

/-- Even the entire image of the minimum map has density zero, expressed
through arbitrary integer upper precision on ordinary counts. -/
theorem minimum_image_sparse : ∀ r, 0<r → ∃ N0, ∀ N, N0≤N →
    r*predicateCount (fun m => ∃ n, orbitMinimum n=m) N≤N := by
  intro r hr
  obtain ⟨N0, hN⟩ := complement_precision
    StoppingNaturalDensity.finite_stopping_time_density_one hr
  refine ⟨N0, ?_⟩
  intro N hn
  have hc := predicateCount_mono (P := fun m => ∃ n, orbitMinimum n=m)
    (Q := fun m => ¬hasFiniteStoppingTime m) (by
      rintro m ⟨n, rfl⟩
      exact minimum_no_drop n) N
  exact Nat.le_trans (Nat.mul_le_mul_left r hc) (hN N hn)

/-- If large-time tails all have density one, the time distribution is not tight. -/
theorem not_tight_of_dense_tails (time : Nat → Nat)
    (h : ∀ K, DensityOne (fun n => K<time n)) : ¬DensityTight time := by
  intro ht
  obtain ⟨K, NT, hT⟩ := ht 2 (by decide)
  obtain ⟨ND, hD⟩ := h K 4 (by decide)
  let N := max NT ND+1
  have hs := hT N (by dsimp [N]; omega)
  have hl := hD N (by dsimp [N]; omega)
  dsimp [N] at hs hl
  omega

/-- Reaching a non-descending orbit point on a density-one set forces the
selected accelerated time to exceed every fixed horizon at density one. -/
theorem terminal_time_dense_tails (time : Nat → Nat)
    (hterminal : DensityOne (fun n => ¬hasFiniteStoppingTime
      (acceleratedOrbit (time n) n))) (K : Nat) : DensityOne (fun n => K<time n) := by
  have hw := density_one_allThrough
    StoppingNaturalDensity.finite_stopping_time_density_one K
  apply densityOne_mono (P := fun n =>
    ¬hasFiniteStoppingTime (acceleratedOrbit (time n) n) ∧
    AllThrough hasFiniteStoppingTime K n) _ (density_one_and hterminal hw)
  intro n hn
  by_cases ht : time n≤K
  · exact False.elim (hn.1 (hn.2 (time n) ht))
  · omega

/-- A terminal-hitting rule on a density-one set cannot satisfy the tight-time
hypothesis used for first-descent density transport. -/
theorem terminal_time_not_tight (time : Nat → Nat)
    (hterminal : DensityOne (fun n => ¬hasFiniteStoppingTime
      (acceleratedOrbit (time n) n))) : ¬DensityTight time :=
  not_tight_of_dense_tails time (terminal_time_dense_tails time hterminal)

/-- Choose an attained minimum time. It need not be the first such time;
its total existence does not supply a computable rule. -/
noncomputable def minimumTime (n : Nat) : Nat :=
  Classical.choose (orbitMinimum_attained n)

/-- The chosen time reaches the canonical orbit minimum. -/
theorem minimumTime_spec (n : Nat) :
    acceleratedOrbit (minimumTime n) n=orbitMinimum n :=
  Classical.choose_spec (orbitMinimum_attained n)

/-- The terminal-time obstruction applies without assuming convergence to 1. -/
theorem minimumTime_dense_tails (K : Nat) : DensityOne (fun n => K<minimumTime n) := by
  apply terminal_time_dense_tails
  apply densityOne_mono (P := hasFiniteStoppingTime) _
    StoppingNaturalDensity.finite_stopping_time_density_one
  intro n _
  rw [minimumTime_spec]
  exact minimum_no_drop n

/-- Pointwise finite minimum times are not uniformly tight in density. -/
theorem minimumTime_not_tight : ¬DensityTight minimumTime :=
  not_tight_of_dense_tails minimumTime minimumTime_dense_tails

/-- Choose a terminal descent round with the proved input-dependent bound. -/
noncomputable def terminalRound (n : Nat) : Nat := Classical.choose (stabilizes n)

/-- The chosen round is at most n and has no further descent. -/
theorem terminalRound_spec (n : Nat) : terminalRound n≤n ∧
    ¬hasFiniteStoppingTime (rounds (terminalRound n) n) := by
  have h := Classical.choose_spec (stabilizes n)
  exact ⟨h.1, (descentMap_fixed_iff _).mp h.2⟩

/-- The number of descent rounds to a terminal state also escapes every fixed
horizon at density one, despite its pointwise upper bound by the input. -/
theorem terminalRound_dense_tails (K : Nat) : DensityOne (fun n => K<terminalRound n) := by
  apply densityOne_mono (P := DropsThrough (K+1)) _ (density_one_dropsThrough (K+1))
  intro n hn
  by_cases ht : terminalRound n≤K
  · exact False.elim ((terminalRound_spec n).2 (hn _ (by omega)))
  · omega

/-- A bound depending on n does not imply density tightness, even for the
actual first-descent rounds. -/
theorem terminalRound_not_tight : ¬DensityTight terminalRound :=
  not_tight_of_dense_tails terminalRound terminalRound_dense_tails

end Collatz.MinimumTransportBarrier
