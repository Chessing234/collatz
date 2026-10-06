import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0521

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 819. -/
theorem bounds_13_819 : exactInterval 13 819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_819 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 819) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_819 : oddCount 819 13 = 6 ∧ acceleratedOrbit 13 819 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_819 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 819) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_819.1, data_13_819.2]

/-- Complete interval computation for depth 13, residue 820. -/
theorem bounds_13_820 : exactInterval 13 820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_820 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 820) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_820 : oddCount 820 13 = 5 ∧ acceleratedOrbit 13 820 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_820 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 820) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_820.1, data_13_820.2]

/-- Complete interval computation for depth 13, residue 821. -/
theorem bounds_13_821 : exactInterval 13 821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_821 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 821) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_821 : oddCount 821 13 = 5 ∧ acceleratedOrbit 13 821 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_821 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 821) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_821.1, data_13_821.2]

/-- Complete interval computation for depth 13, residue 822. -/
theorem bounds_13_822 : exactInterval 13 822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_822 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 822) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_822 : oddCount 822 13 = 8 ∧ acceleratedOrbit 13 822 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_822 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 822) = 3 ^ 8 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_822.1, data_13_822.2]

/-- Complete interval computation for depth 13, residue 823. -/
theorem bounds_13_823 : exactInterval 13 823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_823 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 823) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_823 : oddCount 823 13 = 8 ∧ acceleratedOrbit 13 823 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_823 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 823) = 3 ^ 8 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_823.1, data_13_823.2]

/-- Complete interval computation for depth 13, residue 824. -/
theorem bounds_13_824 : exactInterval 13 824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_824 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 824) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_824 : oddCount 824 13 = 8 ∧ acceleratedOrbit 13 824 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_824 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 824) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_824.1, data_13_824.2]

/-- Complete interval computation for depth 13, residue 825. -/
theorem bounds_13_825 : exactInterval 13 825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_825 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 825) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_825 : oddCount 825 13 = 7 ∧ acceleratedOrbit 13 825 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_825 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 825) = 3 ^ 7 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_825.1, data_13_825.2]

/-- Complete interval computation for depth 13, residue 826. -/
theorem bounds_13_826 : exactInterval 13 826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_826 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 826) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_826 : oddCount 826 13 = 8 ∧ acceleratedOrbit 13 826 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_826 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 826) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_826.1, data_13_826.2]

/-- Complete interval computation for depth 13, residue 827. -/
theorem bounds_13_827 : exactInterval 13 827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_827 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 827) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_827 : oddCount 827 13 = 6 ∧ acceleratedOrbit 13 827 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_827 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 827) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_827.1, data_13_827.2]

/-- Complete interval computation for depth 13, residue 828. -/
theorem bounds_13_828 : exactInterval 13 828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_828 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 828) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_828 : oddCount 828 13 = 8 ∧ acceleratedOrbit 13 828 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_828 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 828) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_828.1, data_13_828.2]

/-- Complete interval computation for depth 13, residue 829. -/
theorem bounds_13_829 : exactInterval 13 829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_829 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 829) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_829 : oddCount 829 13 = 8 ∧ acceleratedOrbit 13 829 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_829 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 829) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_829.1, data_13_829.2]

/-- Complete interval computation for depth 13, residue 830. -/
theorem bounds_13_830 : exactInterval 13 830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_830 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 830) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_830 : oddCount 830 13 = 9 ∧ acceleratedOrbit 13 830 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_830 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 830) = 3 ^ 9 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_830.1, data_13_830.2]

/-- Complete interval computation for depth 13, residue 831. -/
theorem bounds_13_831 : exactInterval 13 831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_831 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 831) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_831 : oddCount 831 13 = 9 ∧ acceleratedOrbit 13 831 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_831 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 831) = 3 ^ 9 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_831.1, data_13_831.2]

/-- Complete interval computation for depth 13, residue 832. -/
theorem bounds_13_832 : exactInterval 13 832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_832 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 832) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_832 : oddCount 832 13 = 2 ∧ acceleratedOrbit 13 832 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_832 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 832) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_832.1, data_13_832.2]

/-- Complete interval computation for depth 13, residue 833. -/
theorem bounds_13_833 : exactInterval 13 833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_833 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 833) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_833 : oddCount 833 13 = 5 ∧ acceleratedOrbit 13 833 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_833 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 833) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_833.1, data_13_833.2]

end Collatz.Research.StoppingAtlas.Batch0521
