import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0780

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4797. -/
theorem bounds_13_4797 : exactInterval 13 4797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4797 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4797) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4797 : oddCount 4797 13 = 7 ∧ acceleratedOrbit 13 4797 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4797 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4797) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4797.1, data_13_4797.2]

/-- Complete interval computation for depth 13, residue 4798. -/
theorem bounds_13_4798 : exactInterval 13 4798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4798 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4798) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4798 : oddCount 4798 13 = 7 ∧ acceleratedOrbit 13 4798 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4798 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4798) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4798.1, data_13_4798.2]

/-- Complete interval computation for depth 13, residue 4799. -/
theorem bounds_13_4799 : exactInterval 13 4799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4799 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4799) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4799 : oddCount 4799 13 = 10 ∧ acceleratedOrbit 13 4799 = 34600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4799 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4799) = 3 ^ 10 * m + 34600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4799.1, data_13_4799.2]

/-- Complete interval computation for depth 13, residue 4800. -/
theorem bounds_13_4800 : exactInterval 13 4800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4800 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4800) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4800 : oddCount 4800 13 = 3 ∧ acceleratedOrbit 13 4800 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4800 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4800) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4800.1, data_13_4800.2]

/-- Complete interval computation for depth 13, residue 4801. -/
theorem bounds_13_4801 : exactInterval 13 4801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4801 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4801) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4801 : oddCount 4801 13 = 5 ∧ acceleratedOrbit 13 4801 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4801 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4801) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4801.1, data_13_4801.2]

/-- Complete interval computation for depth 13, residue 4802. -/
theorem bounds_13_4802 : exactInterval 13 4802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4802 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4802) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4802 : oddCount 4802 13 = 8 ∧ acceleratedOrbit 13 4802 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4802 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4802) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4802.1, data_13_4802.2]

/-- Complete interval computation for depth 13, residue 4803. -/
theorem bounds_13_4803 : exactInterval 13 4803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4803 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4803) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4803 : oddCount 4803 13 = 8 ∧ acceleratedOrbit 13 4803 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4803 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4803) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4803.1, data_13_4803.2]

/-- Complete interval computation for depth 13, residue 4804. -/
theorem bounds_13_4804 : exactInterval 13 4804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4804 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4804) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4804 : oddCount 4804 13 = 6 ∧ acceleratedOrbit 13 4804 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4804 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4804) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4804.1, data_13_4804.2]

/-- Complete interval computation for depth 13, residue 4805. -/
theorem bounds_13_4805 : exactInterval 13 4805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4805 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4805) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4805 : oddCount 4805 13 = 6 ∧ acceleratedOrbit 13 4805 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4805 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4805) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4805.1, data_13_4805.2]

/-- Complete interval computation for depth 13, residue 4806. -/
theorem bounds_13_4806 : exactInterval 13 4806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4806 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4806) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4806 : oddCount 4806 13 = 6 ∧ acceleratedOrbit 13 4806 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4806 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4806) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4806.1, data_13_4806.2]

/-- Complete interval computation for depth 13, residue 4807. -/
theorem bounds_13_4807 : exactInterval 13 4807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4807 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4807) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4807 : oddCount 4807 13 = 6 ∧ acceleratedOrbit 13 4807 = 428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4807 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4807) = 3 ^ 6 * m + 428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4807.1, data_13_4807.2]

/-- Complete interval computation for depth 13, residue 4808. -/
theorem bounds_13_4808 : exactInterval 13 4808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4808 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4808) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4808 : oddCount 4808 13 = 6 ∧ acceleratedOrbit 13 4808 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4808 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4808) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4808.1, data_13_4808.2]

/-- Complete interval computation for depth 13, residue 4809. -/
theorem bounds_13_4809 : exactInterval 13 4809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4809 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4809) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4809 : oddCount 4809 13 = 7 ∧ acceleratedOrbit 13 4809 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4809 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4809) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4809.1, data_13_4809.2]

/-- Complete interval computation for depth 13, residue 4810. -/
theorem bounds_13_4810 : exactInterval 13 4810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4810 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4810) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4810 : oddCount 4810 13 = 6 ∧ acceleratedOrbit 13 4810 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4810 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4810) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4810.1, data_13_4810.2]

/-- Complete interval computation for depth 13, residue 4811. -/
theorem bounds_13_4811 : exactInterval 13 4811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4811 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4811) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4811 : oddCount 4811 13 = 7 ∧ acceleratedOrbit 13 4811 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4811 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4811) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4811.1, data_13_4811.2]

end Collatz.Research.StoppingAtlas.Batch0780
