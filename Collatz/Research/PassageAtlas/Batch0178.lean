import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0178

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5799. -/
theorem bounds_15_5799 : exactInterval 15 5799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5799 : oddCount 5799 15 = 9 ∧ acceleratedOrbit 15 5799 = 3485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5799) = 3 ^ 9 * m + 3485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5799.1, data_15_5799.2]

/-- Complete interval computation for depth 15, residue 5800. -/
theorem bounds_15_5800 : exactInterval 15 5800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5800 : oddCount 5800 15 = 3 ∧ acceleratedOrbit 15 5800 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5800) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5800.1, data_15_5800.2]

/-- Complete interval computation for depth 15, residue 5801. -/
theorem bounds_15_5801 : exactInterval 15 5801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5801 : oddCount 5801 15 = 10 ∧ acceleratedOrbit 15 5801 = 10457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5801) = 3 ^ 10 * m + 10457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5801.1, data_15_5801.2]

/-- Complete interval computation for depth 15, residue 5802. -/
theorem bounds_15_5802 : exactInterval 15 5802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5802 : oddCount 5802 15 = 3 ∧ acceleratedOrbit 15 5802 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5802) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5802.1, data_15_5802.2]

/-- Complete interval computation for depth 15, residue 5803. -/
theorem bounds_15_5803 : exactInterval 15 5803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5803 : oddCount 5803 15 = 8 ∧ acceleratedOrbit 15 5803 = 1163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5803) = 3 ^ 8 * m + 1163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5803.1, data_15_5803.2]

/-- Complete interval computation for depth 15, residue 5804. -/
theorem bounds_15_5804 : exactInterval 15 5804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5804 : oddCount 5804 15 = 7 ∧ acceleratedOrbit 15 5804 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5804) = 3 ^ 7 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5804.1, data_15_5804.2]

/-- Complete interval computation for depth 15, residue 5805. -/
theorem bounds_15_5805 : exactInterval 15 5805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5805 : oddCount 5805 15 = 7 ∧ acceleratedOrbit 15 5805 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5805) = 3 ^ 7 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5805.1, data_15_5805.2]

/-- Complete interval computation for depth 15, residue 5806. -/
theorem bounds_15_5806 : exactInterval 15 5806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5806 : oddCount 5806 15 = 7 ∧ acceleratedOrbit 15 5806 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5806) = 3 ^ 7 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5806.1, data_15_5806.2]

/-- Complete interval computation for depth 15, residue 5807. -/
theorem bounds_15_5807 : exactInterval 15 5807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5807 : oddCount 5807 15 = 10 ∧ acceleratedOrbit 15 5807 = 10469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5807) = 3 ^ 10 * m + 10469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5807.1, data_15_5807.2]

/-- Complete interval computation for depth 15, residue 5808. -/
theorem bounds_15_5808 : exactInterval 15 5808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5808 : oddCount 5808 15 = 6 ∧ acceleratedOrbit 15 5808 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5808) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5808.1, data_15_5808.2]

/-- Complete interval computation for depth 15, residue 5809. -/
theorem bounds_15_5809 : exactInterval 15 5809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5809 : oddCount 5809 15 = 6 ∧ acceleratedOrbit 15 5809 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5809) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5809.1, data_15_5809.2]

/-- Complete interval computation for depth 15, residue 5810. -/
theorem bounds_15_5810 : exactInterval 15 5810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5810 : oddCount 5810 15 = 6 ∧ acceleratedOrbit 15 5810 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5810) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5810.1, data_15_5810.2]

/-- Complete interval computation for depth 15, residue 5811. -/
theorem bounds_15_5811 : exactInterval 15 5811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5811 : oddCount 5811 15 = 6 ∧ acceleratedOrbit 15 5811 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5811) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5811.1, data_15_5811.2]

/-- Complete interval computation for depth 15, residue 5812. -/
theorem bounds_15_5812 : exactInterval 15 5812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5812 : oddCount 5812 15 = 6 ∧ acceleratedOrbit 15 5812 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5812) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5812.1, data_15_5812.2]

/-- Complete interval computation for depth 15, residue 5813. -/
theorem bounds_15_5813 : exactInterval 15 5813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5813 : oddCount 5813 15 = 6 ∧ acceleratedOrbit 15 5813 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5813) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5813.1, data_15_5813.2]

/-- Complete interval computation for depth 15, residue 5814. -/
theorem bounds_15_5814 : exactInterval 15 5814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5814 : oddCount 5814 15 = 8 ∧ acceleratedOrbit 15 5814 = 1165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5814) = 3 ^ 8 * m + 1165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5814.1, data_15_5814.2]

/-- Complete interval computation for depth 15, residue 5815. -/
theorem bounds_15_5815 : exactInterval 15 5815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5815 : oddCount 5815 15 = 8 ∧ acceleratedOrbit 15 5815 = 1165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5815) = 3 ^ 8 * m + 1165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5815.1, data_15_5815.2]

/-- Complete interval computation for depth 15, residue 5816. -/
theorem bounds_15_5816 : exactInterval 15 5816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5816 : oddCount 5816 15 = 6 ∧ acceleratedOrbit 15 5816 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5816) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5816.1, data_15_5816.2]

/-- Complete interval computation for depth 15, residue 5817. -/
theorem bounds_15_5817 : exactInterval 15 5817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5817 : oddCount 5817 15 = 7 ∧ acceleratedOrbit 15 5817 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5817) = 3 ^ 7 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5817.1, data_15_5817.2]

/-- Complete interval computation for depth 15, residue 5818. -/
theorem bounds_15_5818 : exactInterval 15 5818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5818 : oddCount 5818 15 = 6 ∧ acceleratedOrbit 15 5818 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5818) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5818.1, data_15_5818.2]

/-- Complete interval computation for depth 15, residue 5819. -/
theorem bounds_15_5819 : exactInterval 15 5819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5819 : oddCount 5819 15 = 7 ∧ acceleratedOrbit 15 5819 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5819) = 3 ^ 7 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5819.1, data_15_5819.2]

/-- Complete interval computation for depth 15, residue 5820. -/
theorem bounds_15_5820 : exactInterval 15 5820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5820 : oddCount 5820 15 = 7 ∧ acceleratedOrbit 15 5820 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5820) = 3 ^ 7 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5820.1, data_15_5820.2]

/-- Complete interval computation for depth 15, residue 5821. -/
theorem bounds_15_5821 : exactInterval 15 5821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5821 : oddCount 5821 15 = 7 ∧ acceleratedOrbit 15 5821 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5821) = 3 ^ 7 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5821.1, data_15_5821.2]

/-- Complete interval computation for depth 15, residue 5822. -/
theorem bounds_15_5822 : exactInterval 15 5822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5822 : oddCount 5822 15 = 7 ∧ acceleratedOrbit 15 5822 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5822) = 3 ^ 7 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5822.1, data_15_5822.2]

/-- Complete interval computation for depth 15, residue 5823. -/
theorem bounds_15_5823 : exactInterval 15 5823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5823 : oddCount 5823 15 = 10 ∧ acceleratedOrbit 15 5823 = 10496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5823) = 3 ^ 10 * m + 10496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5823.1, data_15_5823.2]

/-- Complete interval computation for depth 15, residue 5824. -/
theorem bounds_15_5824 : exactInterval 15 5824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5824 : oddCount 5824 15 = 7 ∧ acceleratedOrbit 15 5824 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5824) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5824.1, data_15_5824.2]

/-- Complete interval computation for depth 15, residue 5825. -/
theorem bounds_15_5825 : exactInterval 15 5825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5825 : oddCount 5825 15 = 6 ∧ acceleratedOrbit 15 5825 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5825) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5825.1, data_15_5825.2]

/-- Complete interval computation for depth 15, residue 5826. -/
theorem bounds_15_5826 : exactInterval 15 5826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5826 : oddCount 5826 15 = 9 ∧ acceleratedOrbit 15 5826 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5826) = 3 ^ 9 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5826.1, data_15_5826.2]

/-- Complete interval computation for depth 15, residue 5827. -/
theorem bounds_15_5827 : exactInterval 15 5827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5827 : oddCount 5827 15 = 9 ∧ acceleratedOrbit 15 5827 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5827) = 3 ^ 9 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5827.1, data_15_5827.2]

/-- Complete interval computation for depth 15, residue 5828. -/
theorem bounds_15_5828 : exactInterval 15 5828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5828 : oddCount 5828 15 = 5 ∧ acceleratedOrbit 15 5828 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5828) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5828.1, data_15_5828.2]

/-- Complete interval computation for depth 15, residue 5829. -/
theorem bounds_15_5829 : exactInterval 15 5829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5829 : oddCount 5829 15 = 5 ∧ acceleratedOrbit 15 5829 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5829) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5829.1, data_15_5829.2]

/-- Complete interval computation for depth 15, residue 5830. -/
theorem bounds_15_5830 : exactInterval 15 5830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5830 : oddCount 5830 15 = 5 ∧ acceleratedOrbit 15 5830 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5830) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5830.1, data_15_5830.2]

/-- Complete interval computation for depth 15, residue 5831. -/
theorem bounds_15_5831 : exactInterval 15 5831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5831 : oddCount 5831 15 = 6 ∧ acceleratedOrbit 15 5831 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5831) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5831.1, data_15_5831.2]

end Collatz.Research.PassageAtlas.Batch0178
