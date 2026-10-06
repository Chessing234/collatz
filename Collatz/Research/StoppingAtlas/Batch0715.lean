import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0715

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3799. -/
theorem bounds_13_3799 : exactInterval 13 3799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3799 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3799) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3799 : oddCount 3799 13 = 7 ∧ acceleratedOrbit 13 3799 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3799 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3799) = 3 ^ 7 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3799.1, data_13_3799.2]

/-- Complete interval computation for depth 13, residue 3800. -/
theorem bounds_13_3800 : exactInterval 13 3800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3800 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3800) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3800 : oddCount 3800 13 = 5 ∧ acceleratedOrbit 13 3800 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3800 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3800) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3800.1, data_13_3800.2]

/-- Complete interval computation for depth 13, residue 3801. -/
theorem bounds_13_3801 : exactInterval 13 3801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3801 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3801) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3801 : oddCount 3801 13 = 5 ∧ acceleratedOrbit 13 3801 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3801 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3801) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3801.1, data_13_3801.2]

/-- Complete interval computation for depth 13, residue 3802. -/
theorem bounds_13_3802 : exactInterval 13 3802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3802 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3802) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3802 : oddCount 3802 13 = 5 ∧ acceleratedOrbit 13 3802 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3802 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3802) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3802.1, data_13_3802.2]

/-- Complete interval computation for depth 13, residue 3803. -/
theorem bounds_13_3803 : exactInterval 13 3803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3803 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3803) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3803 : oddCount 3803 13 = 9 ∧ acceleratedOrbit 13 3803 = 9143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3803 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3803) = 3 ^ 9 * m + 9143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3803.1, data_13_3803.2]

/-- Complete interval computation for depth 13, residue 3804. -/
theorem bounds_13_3804 : exactInterval 13 3804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3804 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3804) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3804 : oddCount 3804 13 = 5 ∧ acceleratedOrbit 13 3804 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3804 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3804) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3804.1, data_13_3804.2]

/-- Complete interval computation for depth 13, residue 3805. -/
theorem bounds_13_3805 : exactInterval 13 3805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3805 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3805) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3805 : oddCount 3805 13 = 5 ∧ acceleratedOrbit 13 3805 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3805 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3805) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3805.1, data_13_3805.2]

/-- Complete interval computation for depth 13, residue 3806. -/
theorem bounds_13_3806 : exactInterval 13 3806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3806 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3806) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3806 : oddCount 3806 13 = 9 ∧ acceleratedOrbit 13 3806 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3806 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3806) = 3 ^ 9 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3806.1, data_13_3806.2]

/-- Complete interval computation for depth 13, residue 3807. -/
theorem bounds_13_3807 : exactInterval 13 3807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3807 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3807) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3807 : oddCount 3807 13 = 9 ∧ acceleratedOrbit 13 3807 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3807 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3807) = 3 ^ 9 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3807.1, data_13_3807.2]

/-- Complete interval computation for depth 13, residue 3808. -/
theorem bounds_13_3808 : exactInterval 13 3808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3808 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3808) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3808 : oddCount 3808 13 = 4 ∧ acceleratedOrbit 13 3808 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3808 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3808) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3808.1, data_13_3808.2]

/-- Complete interval computation for depth 13, residue 3809. -/
theorem bounds_13_3809 : exactInterval 13 3809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3809 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3809) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3809 : oddCount 3809 13 = 8 ∧ acceleratedOrbit 13 3809 = 3053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3809 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3809) = 3 ^ 8 * m + 3053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3809.1, data_13_3809.2]

/-- Complete interval computation for depth 13, residue 3810. -/
theorem bounds_13_3810 : exactInterval 13 3810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3810 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3810) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3810 : oddCount 3810 13 = 4 ∧ acceleratedOrbit 13 3810 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3810 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3810) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3810.1, data_13_3810.2]

/-- Complete interval computation for depth 13, residue 3811. -/
theorem bounds_13_3811 : exactInterval 13 3811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3811 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3811) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3811 : oddCount 3811 13 = 4 ∧ acceleratedOrbit 13 3811 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3811 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3811) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3811.1, data_13_3811.2]

/-- Complete interval computation for depth 13, residue 3812. -/
theorem bounds_13_3812 : exactInterval 13 3812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3812 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3812) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3812 : oddCount 3812 13 = 6 ∧ acceleratedOrbit 13 3812 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3812 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3812) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3812.1, data_13_3812.2]

/-- Complete interval computation for depth 13, residue 3813. -/
theorem bounds_13_3813 : exactInterval 13 3813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3813 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3813) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3813 : oddCount 3813 13 = 6 ∧ acceleratedOrbit 13 3813 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3813 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3813) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3813.1, data_13_3813.2]

end Collatz.Research.StoppingAtlas.Batch0715
