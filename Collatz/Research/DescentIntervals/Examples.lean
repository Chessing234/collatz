import Collatz.Research.DescentIntervals.Refinement
import Collatz.Research.DescentIntervals.Cycles

/-! Boundary regressions, long trajectories, and symbolic refinement examples. -/
namespace Collatz.Research.DescentIntervals.Examples

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Zero is exceptional on the even ray. -/
theorem even_bounds : exactInterval 1 0 = ⟨1, none⟩ := by decide

theorem even_exact (m : Nat) : stoppingTime (2 * m) 1 ↔ 1 ≤ m := by
  simpa using tail_certificate even_bounds m

/-- One is the exception on the one-mod-four ray. -/
theorem one_mod_four_bounds : exactInterval 2 1 = ⟨1, none⟩ := by decide

theorem one_mod_four_exact (m : Nat) : stoppingTime (4 * m + 1) 2 ↔ 1 ≤ m := by
  simpa using tail_certificate one_mod_four_bounds m

/-- Every positive index in the even refinement clears the one exception. -/
theorem refined_one_mod_four (m : Nat) : stoppingTime (8 * m + 5) 2 := by
  have h : stoppingTime (4 * (2 * m + 1) + 1) 2 :=
    (one_mod_four_exact (2 * m + 1)).mpr (by omega)
  have he : 4 * (2 * m + 1) + 1 = 8 * m + 5 := by omega
  rw [he] at h
  exact h

/-- A nontrivial complete ray. -/
theorem seven_bounds : exactInterval 7 7 = ⟨0, none⟩ := by decide

theorem seven_exact (m : Nat) : stoppingTime (128 * m + 7) 7 := by
  exact (tail_certificate seven_bounds m).mpr (Nat.zero_le _)

/-- Endpoint descent at a later time is not first descent. -/
theorem late_three_bounds : exactInterval 5 3 = ⟨0, some 0⟩ := by decide

theorem late_three_impossible (m : Nat) : ¬ stoppingTime (32 * m + 3) 5 :=
  empty_certificate late_three_bounds m

/-- The familiar long trajectory extends to an infinite exact-time family. -/
theorem twenty_seven_bounds : exactInterval 59 27 = ⟨0, none⟩ := by decide

theorem twenty_seven_exact (m : Nat) : stoppingTime (2 ^ 59 * m + 27) 59 := by
  exact (tail_certificate twenty_seven_bounds m).mpr (Nat.zero_le _)

theorem twenty_seven_endpoint (m : Nat) :
    acceleratedOrbit 59 (2 ^ 59 * m + 27) = 3 ^ 37 * m + 23 := by
  have h : oddCount 27 59 = 37 ∧ acceleratedOrbit 59 27 = 23 := by decide
  rw [Congruence.accOrbit_pow_two_mul_add, h.1, h.2]

/-- The solver handles the earlier weak-contraction research example as well. -/
theorem weak_ray_bounds : exactInterval 65 4591 = ⟨0, none⟩ := by decide

theorem weak_ray_exact (m : Nat) : stoppingTime (2 ^ 65 * m + 4591) 65 := by
  exact (tail_certificate weak_ray_bounds m).mpr (Nat.zero_le _)

/-- The arithmetic solver also supports finite nonempty intervals. -/
theorem finite_arithmetic_interval : solveLE 7 2 3 19 = ⟨0, some 5⟩ := by decide

theorem finite_arithmetic_exact (m : Nat) : 7 * m + 2 ≤ 3 * m + 19 ↔ m < 5 := by
  have h := (solveLE_spec 7 2 3 19 m).symm
  rw [finite_arithmetic_interval] at h
  simpa [IndexInterval.Contains] using h

/-- The point one is the unique two-step periodic member of its dyadic class. -/
theorem trivial_cycle_bounds : periodicInterval 2 1 = ⟨0, some 1⟩ := by decide

theorem trivial_cycle_only (m : Nat) : acceleratedOrbit 2 (4 * m + 1) = 4 * m + 1 ↔ m = 0 := by
  have h := (periodicInterval_spec 2 1 m).symm
  rw [trivial_cycle_bounds] at h
  change (acceleratedOrbit 2 (4 * m + 1) = 4 * m + 1 ↔ 0 ≤ m ∧ m < 1) at h
  omega

/-- A growing all-odd prefix cannot return on the depth-nine Mersenne class. -/
theorem mersenne_no_cycle (m : Nat) : acceleratedOrbit 9 (512 * m + 511) ≠ 512 * m + 511 := by
  have h : periodicInterval 9 511 = noIndices := by decide
  intro he
  have hm := (periodicInterval_spec 9 511 m).mpr he
  rw [h] at hm
  exact not_contains_empty m hm

end Collatz.Research.DescentIntervals.Examples
