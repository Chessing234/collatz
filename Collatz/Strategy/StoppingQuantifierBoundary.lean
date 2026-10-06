import Collatz.Structure.StepDensityTransport
import Collatz.Structure.StoppingNaturalDensity

/-!
# Finite orbit windows versus all future states

This is an example inside the actual Collatz system. Every fixed finite orbit
window has finite stopping time at all its states for almost every start.
Yet no start has finite stopping time at every future state. Well-foundedness
of the natural numbers forces some visited state never to drop below itself.
There is no contradiction: countable intersections need not preserve density.
-/
namespace Collatz.StoppingQuantifierBoundary
open NaturalDensity StepDensityTransport

/-- Every fixed window has the finite-stopping property at density one. -/
theorem density_one_stopping_windows (K : Nat) :
    DensityOne (AllThrough hasFiniteStoppingTime K) :=
  density_one_allThrough StoppingNaturalDensity.finite_stopping_time_density_one K

/-- No orbit can keep supplying strict descent at every visited state.
Otherwise strong induction follows the next descent to a smaller counterexample. -/
theorem not_all_states_stop (n : Nat) :
    ¬(∀ k, hasFiniteStoppingTime (acceleratedOrbit k n)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hall
    have hstart := hall 0
    obtain ⟨j, _, hj⟩ := hstart
    apply ih (acceleratedOrbit j n) hj
    intro k
    have ht := hall (k+j)
    rw [← acceleratedOrbit_add] at ht
    exact ht

/-- Every orbit visits a never-dropping state; its value need not be known.
Proving that every positive such state is 1 is a separate universal-descent task. -/
theorem visits_never_dropper (n : Nat) :
    ∃ k, ¬hasFiniteStoppingTime (acceleratedOrbit k n) := by
  classical
  by_cases hex : ∃ k, ¬hasFiniteStoppingTime (acceleratedOrbit k n)
  · exact hex
  · apply False.elim
    apply not_all_states_stop n
    intro k
    by_cases hk : hasFiniteStoppingTime (acceleratedOrbit k n)
    · exact hk
    · exact False.elim (hex ⟨k, hk⟩)

/-- The intersection of all these finite-window predicates is empty. -/
theorem stopping_windows_intersection_empty (n : Nat) :
    ¬(∀ K, AllThrough hasFiniteStoppingTime K n) := by
  intro h
  apply not_all_states_stop n
  intro k
  exact h k k (Nat.le_refl _)

/-- A concrete failure of countable-intersection closure for density one,
using actual Collatz stopping times rather than a comparison dynamical system. -/
theorem density_one_windows_with_empty_intersection :
    (∀ K, DensityOne (AllThrough hasFiniteStoppingTime K)) ∧
      ∀ n, ¬(∀ K, AllThrough hasFiniteStoppingTime K n) :=
  ⟨density_one_stopping_windows, stopping_windows_intersection_empty⟩

end Collatz.StoppingQuantifierBoundary
