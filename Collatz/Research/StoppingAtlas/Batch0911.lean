import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0911

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6809. -/
theorem bounds_13_6809 : exactInterval 13 6809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6809 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6809) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6809 : oddCount 6809 13 = 7 ∧ acceleratedOrbit 13 6809 = 1819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6809 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6809) = 3 ^ 7 * m + 1819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6809.1, data_13_6809.2]

/-- Complete interval computation for depth 13, residue 6810. -/
theorem bounds_13_6810 : exactInterval 13 6810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6810 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6810) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6810 : oddCount 6810 13 = 7 ∧ acceleratedOrbit 13 6810 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6810 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6810) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6810.1, data_13_6810.2]

/-- Complete interval computation for depth 13, residue 6811. -/
theorem bounds_13_6811 : exactInterval 13 6811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6811 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6811) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6811 : oddCount 6811 13 = 10 ∧ acceleratedOrbit 13 6811 = 49106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6811 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6811) = 3 ^ 10 * m + 49106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6811.1, data_13_6811.2]

/-- Complete interval computation for depth 13, residue 6812. -/
theorem bounds_13_6812 : exactInterval 13 6812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6812 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6812) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6812 : oddCount 6812 13 = 7 ∧ acceleratedOrbit 13 6812 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6812 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6812) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6812.1, data_13_6812.2]

/-- Complete interval computation for depth 13, residue 6813. -/
theorem bounds_13_6813 : exactInterval 13 6813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6813 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6813) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6813 : oddCount 6813 13 = 7 ∧ acceleratedOrbit 13 6813 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6813 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6813) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6813.1, data_13_6813.2]

/-- Complete interval computation for depth 13, residue 6814. -/
theorem bounds_13_6814 : exactInterval 13 6814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6814 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6814) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6814 : oddCount 6814 13 = 7 ∧ acceleratedOrbit 13 6814 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6814 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6814) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6814.1, data_13_6814.2]

/-- Complete interval computation for depth 13, residue 6815. -/
theorem bounds_13_6815 : exactInterval 13 6815 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6815 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6815) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6815 : oddCount 6815 13 = 8 ∧ acceleratedOrbit 13 6815 = 5459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6815 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6815) = 3 ^ 8 * m + 5459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6815.1, data_13_6815.2]

/-- Complete interval computation for depth 13, residue 6816. -/
theorem bounds_13_6816 : exactInterval 13 6816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6816 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6816) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6816 : oddCount 6816 13 = 2 ∧ acceleratedOrbit 13 6816 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6816 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6816) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6816.1, data_13_6816.2]

/-- Complete interval computation for depth 13, residue 6817. -/
theorem bounds_13_6817 : exactInterval 13 6817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6817 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6817) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6817 : oddCount 6817 13 = 9 ∧ acceleratedOrbit 13 6817 = 16388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6817 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6817) = 3 ^ 9 * m + 16388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6817.1, data_13_6817.2]

/-- Complete interval computation for depth 13, residue 6818. -/
theorem bounds_13_6818 : exactInterval 13 6818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6818 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6818) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6818 : oddCount 6818 13 = 8 ∧ acceleratedOrbit 13 6818 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6818 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6818) = 3 ^ 8 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6818.1, data_13_6818.2]

/-- Complete interval computation for depth 13, residue 6819. -/
theorem bounds_13_6819 : exactInterval 13 6819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6819 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6819) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6819 : oddCount 6819 13 = 8 ∧ acceleratedOrbit 13 6819 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6819 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6819) = 3 ^ 8 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6819.1, data_13_6819.2]

/-- Complete interval computation for depth 13, residue 6820. -/
theorem bounds_13_6820 : exactInterval 13 6820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6820 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6820) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6820 : oddCount 6820 13 = 9 ∧ acceleratedOrbit 13 6820 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6820 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6820) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6820.1, data_13_6820.2]

/-- Complete interval computation for depth 13, residue 6821. -/
theorem bounds_13_6821 : exactInterval 13 6821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6821 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6821) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6821 : oddCount 6821 13 = 9 ∧ acceleratedOrbit 13 6821 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6821 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6821) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6821.1, data_13_6821.2]

/-- Complete interval computation for depth 13, residue 6822. -/
theorem bounds_13_6822 : exactInterval 13 6822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6822 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6822) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6822 : oddCount 6822 13 = 9 ∧ acceleratedOrbit 13 6822 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6822 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6822) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6822.1, data_13_6822.2]

/-- Complete interval computation for depth 13, residue 6823. -/
theorem bounds_13_6823 : exactInterval 13 6823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6823 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6823) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6823 : oddCount 6823 13 = 10 ∧ acceleratedOrbit 13 6823 = 49193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6823 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6823) = 3 ^ 10 * m + 49193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6823.1, data_13_6823.2]

end Collatz.Research.StoppingAtlas.Batch0911
