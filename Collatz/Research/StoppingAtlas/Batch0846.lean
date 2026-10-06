import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0846

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5811. -/
theorem bounds_13_5811 : exactInterval 13 5811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5811 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5811) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5811 : oddCount 5811 13 = 5 ∧ acceleratedOrbit 13 5811 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5811 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5811) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5811.1, data_13_5811.2]

/-- Complete interval computation for depth 13, residue 5812. -/
theorem bounds_13_5812 : exactInterval 13 5812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5812 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5812) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5812 : oddCount 5812 13 = 5 ∧ acceleratedOrbit 13 5812 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5812 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5812) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5812.1, data_13_5812.2]

/-- Complete interval computation for depth 13, residue 5813. -/
theorem bounds_13_5813 : exactInterval 13 5813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5813 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5813) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5813 : oddCount 5813 13 = 5 ∧ acceleratedOrbit 13 5813 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5813 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5813) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5813.1, data_13_5813.2]

/-- Complete interval computation for depth 13, residue 5814. -/
theorem bounds_13_5814 : exactInterval 13 5814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5814 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5814) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5814 : oddCount 5814 13 = 7 ∧ acceleratedOrbit 13 5814 = 1553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5814 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5814) = 3 ^ 7 * m + 1553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5814.1, data_13_5814.2]

/-- Complete interval computation for depth 13, residue 5815. -/
theorem bounds_13_5815 : exactInterval 13 5815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5815 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5815) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5815 : oddCount 5815 13 = 7 ∧ acceleratedOrbit 13 5815 = 1553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5815 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5815) = 3 ^ 7 * m + 1553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5815.1, data_13_5815.2]

/-- Complete interval computation for depth 13, residue 5816. -/
theorem bounds_13_5816 : exactInterval 13 5816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5816 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5816) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5816 : oddCount 5816 13 = 5 ∧ acceleratedOrbit 13 5816 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5816 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5816) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5816.1, data_13_5816.2]

/-- Complete interval computation for depth 13, residue 5817. -/
theorem bounds_13_5817 : exactInterval 13 5817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5817 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5817) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5817 : oddCount 5817 13 = 6 ∧ acceleratedOrbit 13 5817 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5817 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5817) = 3 ^ 6 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5817.1, data_13_5817.2]

/-- Complete interval computation for depth 13, residue 5818. -/
theorem bounds_13_5818 : exactInterval 13 5818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5818 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5818) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5818 : oddCount 5818 13 = 5 ∧ acceleratedOrbit 13 5818 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5818 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5818) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5818.1, data_13_5818.2]

/-- Complete interval computation for depth 13, residue 5819. -/
theorem bounds_13_5819 : exactInterval 13 5819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5819 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5819) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5819 : oddCount 5819 13 = 6 ∧ acceleratedOrbit 13 5819 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5819 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5819) = 3 ^ 6 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5819.1, data_13_5819.2]

/-- Complete interval computation for depth 13, residue 5820. -/
theorem bounds_13_5820 : exactInterval 13 5820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5820 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5820) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5820 : oddCount 5820 13 = 7 ∧ acceleratedOrbit 13 5820 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5820 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5820) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5820.1, data_13_5820.2]

/-- Complete interval computation for depth 13, residue 5821. -/
theorem bounds_13_5821 : exactInterval 13 5821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5821 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5821) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5821 : oddCount 5821 13 = 7 ∧ acceleratedOrbit 13 5821 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5821 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5821) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5821.1, data_13_5821.2]

/-- Complete interval computation for depth 13, residue 5822. -/
theorem bounds_13_5822 : exactInterval 13 5822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5822 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5822) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5822 : oddCount 5822 13 = 7 ∧ acceleratedOrbit 13 5822 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5822 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5822) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5822.1, data_13_5822.2]

/-- Complete interval computation for depth 13, residue 5823. -/
theorem bounds_13_5823 : exactInterval 13 5823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5823 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5823) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5823 : oddCount 5823 13 = 9 ∧ acceleratedOrbit 13 5823 = 13994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5823 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5823) = 3 ^ 9 * m + 13994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5823.1, data_13_5823.2]

/-- Complete interval computation for depth 13, residue 5824. -/
theorem bounds_13_5824 : exactInterval 13 5824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5824 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5824) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5824 : oddCount 5824 13 = 5 ∧ acceleratedOrbit 13 5824 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5824 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5824) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5824.1, data_13_5824.2]

/-- Complete interval computation for depth 13, residue 5825. -/
theorem bounds_13_5825 : exactInterval 13 5825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5825 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5825) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5825 : oddCount 5825 13 = 5 ∧ acceleratedOrbit 13 5825 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5825 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5825) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5825.1, data_13_5825.2]

end Collatz.Research.StoppingAtlas.Batch0846
