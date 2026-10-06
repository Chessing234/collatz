import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0910

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6794. -/
theorem bounds_13_6794 : exactInterval 13 6794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6794 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6794) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6794 : oddCount 6794 13 = 6 ∧ acceleratedOrbit 13 6794 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6794 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6794) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6794.1, data_13_6794.2]

/-- Complete interval computation for depth 13, residue 6795. -/
theorem bounds_13_6795 : exactInterval 13 6795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6795 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6795) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6795 : oddCount 6795 13 = 6 ∧ acceleratedOrbit 13 6795 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6795 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6795) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6795.1, data_13_6795.2]

/-- Complete interval computation for depth 13, residue 6796. -/
theorem bounds_13_6796 : exactInterval 13 6796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6796 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6796) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6796 : oddCount 6796 13 = 6 ∧ acceleratedOrbit 13 6796 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6796 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6796) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6796.1, data_13_6796.2]

/-- Complete interval computation for depth 13, residue 6797. -/
theorem bounds_13_6797 : exactInterval 13 6797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6797 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6797) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6797 : oddCount 6797 13 = 6 ∧ acceleratedOrbit 13 6797 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6797 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6797) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6797.1, data_13_6797.2]

/-- Complete interval computation for depth 13, residue 6798. -/
theorem bounds_13_6798 : exactInterval 13 6798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6798 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6798) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6798 : oddCount 6798 13 = 8 ∧ acceleratedOrbit 13 6798 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6798 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6798) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6798.1, data_13_6798.2]

/-- Complete interval computation for depth 13, residue 6799. -/
theorem bounds_13_6799 : exactInterval 13 6799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6799 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6799) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6799 : oddCount 6799 13 = 8 ∧ acceleratedOrbit 13 6799 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6799 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6799) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6799.1, data_13_6799.2]

/-- Complete interval computation for depth 13, residue 6800. -/
theorem bounds_13_6800 : exactInterval 13 6800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6800 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6800) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6800 : oddCount 6800 13 = 7 ∧ acceleratedOrbit 13 6800 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6800 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6800) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6800.1, data_13_6800.2]

/-- Complete interval computation for depth 13, residue 6801. -/
theorem bounds_13_6801 : exactInterval 13 6801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6801 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6801) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6801 : oddCount 6801 13 = 8 ∧ acceleratedOrbit 13 6801 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6801 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6801) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6801.1, data_13_6801.2]

/-- Complete interval computation for depth 13, residue 6802. -/
theorem bounds_13_6802 : exactInterval 13 6802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6802 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6802) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6802 : oddCount 6802 13 = 8 ∧ acceleratedOrbit 13 6802 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6802 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6802) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6802.1, data_13_6802.2]

/-- Complete interval computation for depth 13, residue 6803. -/
theorem bounds_13_6803 : exactInterval 13 6803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6803 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6803) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6803 : oddCount 6803 13 = 8 ∧ acceleratedOrbit 13 6803 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6803 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6803) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6803.1, data_13_6803.2]

/-- Complete interval computation for depth 13, residue 6804. -/
theorem bounds_13_6804 : exactInterval 13 6804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6804 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6804) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6804 : oddCount 6804 13 = 7 ∧ acceleratedOrbit 13 6804 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6804 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6804) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6804.1, data_13_6804.2]

/-- Complete interval computation for depth 13, residue 6805. -/
theorem bounds_13_6805 : exactInterval 13 6805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6805 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6805) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6805 : oddCount 6805 13 = 7 ∧ acceleratedOrbit 13 6805 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6805 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6805) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6805.1, data_13_6805.2]

/-- Complete interval computation for depth 13, residue 6806. -/
theorem bounds_13_6806 : exactInterval 13 6806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6806 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6806) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6806 : oddCount 6806 13 = 6 ∧ acceleratedOrbit 13 6806 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6806 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6806) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6806.1, data_13_6806.2]

/-- Complete interval computation for depth 13, residue 6807. -/
theorem bounds_13_6807 : exactInterval 13 6807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6807 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6807) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6807 : oddCount 6807 13 = 6 ∧ acceleratedOrbit 13 6807 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6807 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6807) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6807.1, data_13_6807.2]

/-- Complete interval computation for depth 13, residue 6808. -/
theorem bounds_13_6808 : exactInterval 13 6808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6808 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6808) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6808 : oddCount 6808 13 = 7 ∧ acceleratedOrbit 13 6808 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6808 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6808) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6808.1, data_13_6808.2]

end Collatz.Research.StoppingAtlas.Batch0910
