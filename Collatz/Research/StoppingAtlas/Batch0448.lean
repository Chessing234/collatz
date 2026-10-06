import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0448

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3793. -/
theorem bounds_12_3793 : exactInterval 12 3793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3793 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3793) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3793 : oddCount 3793 12 = 6 ∧ acceleratedOrbit 12 3793 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3793 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3793) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3793.1, data_12_3793.2]

/-- Complete interval computation for depth 12, residue 3794. -/
theorem bounds_12_3794 : exactInterval 12 3794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3794 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3794) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3794 : oddCount 3794 12 = 6 ∧ acceleratedOrbit 12 3794 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3794 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3794) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3794.1, data_12_3794.2]

/-- Complete interval computation for depth 12, residue 3795. -/
theorem bounds_12_3795 : exactInterval 12 3795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3795 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3795) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3795 : oddCount 3795 12 = 6 ∧ acceleratedOrbit 12 3795 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3795 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3795) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3795.1, data_12_3795.2]

/-- Complete interval computation for depth 12, residue 3796. -/
theorem bounds_12_3796 : exactInterval 12 3796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3796 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3796) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3796 : oddCount 3796 12 = 4 ∧ acceleratedOrbit 12 3796 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3796 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3796) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3796.1, data_12_3796.2]

/-- Complete interval computation for depth 12, residue 3797. -/
theorem bounds_12_3797 : exactInterval 12 3797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3797 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3797) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3797 : oddCount 3797 12 = 4 ∧ acceleratedOrbit 12 3797 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3797 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3797) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3797.1, data_12_3797.2]

/-- Complete interval computation for depth 12, residue 3798. -/
theorem bounds_12_3798 : exactInterval 12 3798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3798 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3798) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3798 : oddCount 3798 12 = 6 ∧ acceleratedOrbit 12 3798 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3798 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3798) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3798.1, data_12_3798.2]

/-- Complete interval computation for depth 12, residue 3799. -/
theorem bounds_12_3799 : exactInterval 12 3799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3799 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3799) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3799 : oddCount 3799 12 = 6 ∧ acceleratedOrbit 12 3799 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3799 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3799) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3799.1, data_12_3799.2]

/-- Complete interval computation for depth 12, residue 3800. -/
theorem bounds_12_3800 : exactInterval 12 3800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3800 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3800) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3800 : oddCount 3800 12 = 5 ∧ acceleratedOrbit 12 3800 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3800 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3800) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3800.1, data_12_3800.2]

/-- Complete interval computation for depth 12, residue 3801. -/
theorem bounds_12_3801 : exactInterval 12 3801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3801 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3801) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3801 : oddCount 3801 12 = 5 ∧ acceleratedOrbit 12 3801 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3801 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3801) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3801.1, data_12_3801.2]

/-- Complete interval computation for depth 12, residue 3802. -/
theorem bounds_12_3802 : exactInterval 12 3802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3802 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3802) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3802 : oddCount 3802 12 = 5 ∧ acceleratedOrbit 12 3802 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3802 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3802) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3802.1, data_12_3802.2]

/-- Complete interval computation for depth 12, residue 3803. -/
theorem bounds_12_3803 : exactInterval 12 3803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3803 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3803) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3803 : oddCount 3803 12 = 8 ∧ acceleratedOrbit 12 3803 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3803 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3803) = 3 ^ 8 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3803.1, data_12_3803.2]

/-- Complete interval computation for depth 12, residue 3804. -/
theorem bounds_12_3804 : exactInterval 12 3804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3804 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3804) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3804 : oddCount 3804 12 = 5 ∧ acceleratedOrbit 12 3804 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3804 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3804) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3804.1, data_12_3804.2]

/-- Complete interval computation for depth 12, residue 3805. -/
theorem bounds_12_3805 : exactInterval 12 3805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3805 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3805) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3805 : oddCount 3805 12 = 5 ∧ acceleratedOrbit 12 3805 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3805 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3805) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3805.1, data_12_3805.2]

/-- Complete interval computation for depth 12, residue 3806. -/
theorem bounds_12_3806 : exactInterval 12 3806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3806 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3806) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3806 : oddCount 3806 12 = 8 ∧ acceleratedOrbit 12 3806 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3806 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3806) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3806.1, data_12_3806.2]

/-- Complete interval computation for depth 12, residue 3807. -/
theorem bounds_12_3807 : exactInterval 12 3807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3807 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3807) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3807 : oddCount 3807 12 = 8 ∧ acceleratedOrbit 12 3807 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3807 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3807) = 3 ^ 8 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3807.1, data_12_3807.2]

/-- Complete interval computation for depth 12, residue 3808. -/
theorem bounds_12_3808 : exactInterval 12 3808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3808 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3808) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3808 : oddCount 3808 12 = 4 ∧ acceleratedOrbit 12 3808 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3808 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3808) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3808.1, data_12_3808.2]

end Collatz.Research.StoppingAtlas.Batch0448
