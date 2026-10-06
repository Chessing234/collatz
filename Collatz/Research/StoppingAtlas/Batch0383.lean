import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0383

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2795. -/
theorem bounds_12_2795 : exactInterval 12 2795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2795 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2795) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2795 : oddCount 2795 12 = 8 ∧ acceleratedOrbit 12 2795 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2795 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2795) = 3 ^ 8 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2795.1, data_12_2795.2]

/-- Complete interval computation for depth 12, residue 2796. -/
theorem bounds_12_2796 : exactInterval 12 2796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2796 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2796) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2796 : oddCount 2796 12 = 6 ∧ acceleratedOrbit 12 2796 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2796 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2796) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2796.1, data_12_2796.2]

/-- Complete interval computation for depth 12, residue 2797. -/
theorem bounds_12_2797 : exactInterval 12 2797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2797 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2797) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2797 : oddCount 2797 12 = 6 ∧ acceleratedOrbit 12 2797 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2797 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2797) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2797.1, data_12_2797.2]

/-- Complete interval computation for depth 12, residue 2798. -/
theorem bounds_12_2798 : exactInterval 12 2798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2798 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2798) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2798 : oddCount 2798 12 = 6 ∧ acceleratedOrbit 12 2798 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2798 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2798) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2798.1, data_12_2798.2]

/-- Complete interval computation for depth 12, residue 2799. -/
theorem bounds_12_2799 : exactInterval 12 2799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2799 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2799) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2799 : oddCount 2799 12 = 9 ∧ acceleratedOrbit 12 2799 = 13456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2799 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2799) = 3 ^ 9 * m + 13456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2799.1, data_12_2799.2]

/-- Complete interval computation for depth 12, residue 2800. -/
theorem bounds_12_2800 : exactInterval 12 2800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2800 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2800) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2800 : oddCount 2800 12 = 5 ∧ acceleratedOrbit 12 2800 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2800 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2800) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2800.1, data_12_2800.2]

/-- Complete interval computation for depth 12, residue 2801. -/
theorem bounds_12_2801 : exactInterval 12 2801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2801 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2801) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2801 : oddCount 2801 12 = 4 ∧ acceleratedOrbit 12 2801 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2801 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2801) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2801.1, data_12_2801.2]

/-- Complete interval computation for depth 12, residue 2802. -/
theorem bounds_12_2802 : exactInterval 12 2802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2802 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2802) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2802 : oddCount 2802 12 = 8 ∧ acceleratedOrbit 12 2802 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2802 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2802) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2802.1, data_12_2802.2]

/-- Complete interval computation for depth 12, residue 2803. -/
theorem bounds_12_2803 : exactInterval 12 2803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2803 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2803) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2803 : oddCount 2803 12 = 8 ∧ acceleratedOrbit 12 2803 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2803 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2803) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2803.1, data_12_2803.2]

/-- Complete interval computation for depth 12, residue 2804. -/
theorem bounds_12_2804 : exactInterval 12 2804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2804 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2804) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2804 : oddCount 2804 12 = 5 ∧ acceleratedOrbit 12 2804 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2804 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2804) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2804.1, data_12_2804.2]

/-- Complete interval computation for depth 12, residue 2805. -/
theorem bounds_12_2805 : exactInterval 12 2805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2805 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2805) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2805 : oddCount 2805 12 = 5 ∧ acceleratedOrbit 12 2805 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2805 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2805) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2805.1, data_12_2805.2]

/-- Complete interval computation for depth 12, residue 2806. -/
theorem bounds_12_2806 : exactInterval 12 2806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2806 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2806) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2806 : oddCount 2806 12 = 6 ∧ acceleratedOrbit 12 2806 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2806 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2806) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2806.1, data_12_2806.2]

/-- Complete interval computation for depth 12, residue 2807. -/
theorem bounds_12_2807 : exactInterval 12 2807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2807 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2807) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2807 : oddCount 2807 12 = 6 ∧ acceleratedOrbit 12 2807 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2807 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2807) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2807.1, data_12_2807.2]

/-- Complete interval computation for depth 12, residue 2808. -/
theorem bounds_12_2808 : exactInterval 12 2808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2808 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2808) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2808 : oddCount 2808 12 = 5 ∧ acceleratedOrbit 12 2808 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2808 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2808) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2808.1, data_12_2808.2]

/-- Complete interval computation for depth 12, residue 2809. -/
theorem bounds_12_2809 : exactInterval 12 2809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2809 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2809) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2809 : oddCount 2809 12 = 7 ∧ acceleratedOrbit 12 2809 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2809 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2809) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2809.1, data_12_2809.2]

end Collatz.Research.StoppingAtlas.Batch0383
