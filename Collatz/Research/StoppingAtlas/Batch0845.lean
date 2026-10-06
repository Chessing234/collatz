import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0845

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5795. -/
theorem bounds_13_5795 : exactInterval 13 5795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5795 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5795) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5795 : oddCount 5795 13 = 7 ∧ acceleratedOrbit 13 5795 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5795 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5795) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5795.1, data_13_5795.2]

/-- Complete interval computation for depth 13, residue 5796. -/
theorem bounds_13_5796 : exactInterval 13 5796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5796 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5796) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5796 : oddCount 5796 13 = 7 ∧ acceleratedOrbit 13 5796 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5796 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5796) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5796.1, data_13_5796.2]

/-- Complete interval computation for depth 13, residue 5797. -/
theorem bounds_13_5797 : exactInterval 13 5797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5797 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5797) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5797 : oddCount 5797 13 = 7 ∧ acceleratedOrbit 13 5797 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5797 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5797) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5797.1, data_13_5797.2]

/-- Complete interval computation for depth 13, residue 5798. -/
theorem bounds_13_5798 : exactInterval 13 5798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5798 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5798) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5798 : oddCount 5798 13 = 7 ∧ acceleratedOrbit 13 5798 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5798 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5798) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5798.1, data_13_5798.2]

/-- Complete interval computation for depth 13, residue 5799. -/
theorem bounds_13_5799 : exactInterval 13 5799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5799 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5799) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5799 : oddCount 5799 13 = 8 ∧ acceleratedOrbit 13 5799 = 4646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5799 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5799) = 3 ^ 8 * m + 4646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5799.1, data_13_5799.2]

/-- Complete interval computation for depth 13, residue 5800. -/
theorem bounds_13_5800 : exactInterval 13 5800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5800 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5800) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5800 : oddCount 5800 13 = 3 ∧ acceleratedOrbit 13 5800 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5800 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5800) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5800.1, data_13_5800.2]

/-- Complete interval computation for depth 13, residue 5801. -/
theorem bounds_13_5801 : exactInterval 13 5801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5801 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5801) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5801 : oddCount 5801 13 = 9 ∧ acceleratedOrbit 13 5801 = 13942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5801 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5801) = 3 ^ 9 * m + 13942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5801.1, data_13_5801.2]

/-- Complete interval computation for depth 13, residue 5802. -/
theorem bounds_13_5802 : exactInterval 13 5802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5802 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5802) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5802 : oddCount 5802 13 = 3 ∧ acceleratedOrbit 13 5802 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5802 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5802) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5802.1, data_13_5802.2]

/-- Complete interval computation for depth 13, residue 5803. -/
theorem bounds_13_5803 : exactInterval 13 5803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5803 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5803) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5803 : oddCount 5803 13 = 7 ∧ acceleratedOrbit 13 5803 = 1550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5803 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5803) = 3 ^ 7 * m + 1550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5803.1, data_13_5803.2]

/-- Complete interval computation for depth 13, residue 5804. -/
theorem bounds_13_5804 : exactInterval 13 5804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5804 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5804) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5804 : oddCount 5804 13 = 7 ∧ acceleratedOrbit 13 5804 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5804 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5804) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5804.1, data_13_5804.2]

/-- Complete interval computation for depth 13, residue 5805. -/
theorem bounds_13_5805 : exactInterval 13 5805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5805 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5805) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5805 : oddCount 5805 13 = 7 ∧ acceleratedOrbit 13 5805 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5805 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5805) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5805.1, data_13_5805.2]

/-- Complete interval computation for depth 13, residue 5806. -/
theorem bounds_13_5806 : exactInterval 13 5806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5806 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5806) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5806 : oddCount 5806 13 = 7 ∧ acceleratedOrbit 13 5806 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5806 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5806) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5806.1, data_13_5806.2]

/-- Complete interval computation for depth 13, residue 5807. -/
theorem bounds_13_5807 : exactInterval 13 5807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5807 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5807) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5807 : oddCount 5807 13 = 9 ∧ acceleratedOrbit 13 5807 = 13958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5807 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5807) = 3 ^ 9 * m + 13958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5807.1, data_13_5807.2]

/-- Complete interval computation for depth 13, residue 5808. -/
theorem bounds_13_5808 : exactInterval 13 5808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5808 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5808) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5808 : oddCount 5808 13 = 5 ∧ acceleratedOrbit 13 5808 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5808 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5808) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5808.1, data_13_5808.2]

/-- Complete interval computation for depth 13, residue 5809. -/
theorem bounds_13_5809 : exactInterval 13 5809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5809 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5809) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5809 : oddCount 5809 13 = 5 ∧ acceleratedOrbit 13 5809 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5809 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5809) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5809.1, data_13_5809.2]

/-- Complete interval computation for depth 13, residue 5810. -/
theorem bounds_13_5810 : exactInterval 13 5810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5810 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5810) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5810 : oddCount 5810 13 = 5 ∧ acceleratedOrbit 13 5810 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5810 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5810) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5810.1, data_13_5810.2]

end Collatz.Research.StoppingAtlas.Batch0845
