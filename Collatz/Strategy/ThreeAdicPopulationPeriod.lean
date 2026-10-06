import Collatz.Strategy.ThreeAdicEscapeTime
import Collatz.Strategy.ThreeAdicPopulationWindows

/-!
# The exact minimal input period of the orbit residue

The period `3*2^k` is forced by the residue-zero fiber. It is not merely a
convenient upper bound. Any period of the complete residue-valued function
must be a multiple of it. The input period therefore grows without bound.
-/

namespace Collatz.ThreeAdicPopulation

/-- A period of the full residue-valued orbit function, including residue zero. -/
def IsResiduePeriod (k d : Nat) : Prop :=
  ∀ n : Nat, acceleratedOrbit k (n + d) % 3 = acceleratedOrbit k n % 3

/-- The totalized orbit at zero stays at zero. -/
theorem orbit_zero_state (k : Nat) : acceleratedOrbit k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [acceleratedOrbit, ih]

/-- Every period is a multiple of the constructed period. -/
theorem period_dvd_of_isResiduePeriod {k d : Nat} (h : IsResiduePeriod k d) :
    period k ∣ d := by
  have hz := h 0
  simp only [Nat.zero_add, orbit_zero_state, Nat.zero_mod] at hz
  exact (ThreeAdicEscape.orbit_divisible_three_iff k d).mp
    (Nat.dvd_of_mod_eq_zero hz)

/-- Every multiple of the constructed period is a period. -/
theorem isResiduePeriod_of_period_dvd {k d : Nat} (h : period k ∣ d) :
    IsResiduePeriod k d := by
  obtain ⟨q, hq⟩ := h
  intro n
  rw [hq, Nat.add_comm]
  exact orbit_mod_three_periodic k n q

/-- Exact classification of all residue periods, including the zero shift. -/
theorem isResiduePeriod_iff (k d : Nat) : IsResiduePeriod k d ↔ period k ∣ d :=
  ⟨period_dvd_of_isResiduePeriod, isResiduePeriod_of_period_dvd⟩

/-- The constructed positive period is genuinely the smallest positive period. -/
theorem period_minimal {k d : Nat} (hd : 0 < d) (h : IsResiduePeriod k d) :
    period k ≤ d := Nat.le_of_dvd hd (period_dvd_of_isResiduePeriod h)

/-- A smaller positive shift cannot preserve all orbit residues. -/
theorem no_smaller_period {k d : Nat} (hd : 0 < d) (hsize : d < period k) :
    ¬ IsResiduePeriod k d := by
  intro h
  have hm := period_minimal hd h
  omega

/-- A concrete distinguishing input for every nonperiod shift is zero. -/
theorem zero_distinguishes_nonperiod {k d : Nat} (hd : ¬ period k ∣ d) :
    acceleratedOrbit k d % 3 ≠ acceleratedOrbit k 0 % 3 := by
  rw [orbit_zero_state, Nat.zero_mod]
  intro hz
  exact hd ((ThreeAdicEscape.orbit_divisible_three_iff k d).mp
    (Nat.dvd_of_mod_eq_zero hz))

/-- No fixed positive period describes the residue function at every depth. -/
theorem no_depth_uniform_period :
    ¬ ∃ d : Nat, 0 < d ∧ ∀ k : Nat, IsResiduePeriod k d := by
  rintro ⟨d, hd, hall⟩
  have hp := period_minimal hd (hall d)
  have hg := ThreeAdicEscape.self_lt_two_pow d
  unfold period at hp
  omega

end Collatz.ThreeAdicPopulation
