import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0121

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 819. -/
theorem bounds_11_819 : exactInterval 11 819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_819 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 819) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_819 : oddCount 819 11 = 5 ∧ acceleratedOrbit 11 819 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_819 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 819) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_819.1, data_11_819.2]

/-- Complete interval computation for depth 11, residue 820. -/
theorem bounds_11_820 : exactInterval 11 820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_820 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 820) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_820 : oddCount 820 11 = 3 ∧ acceleratedOrbit 11 820 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_820 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 820) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_820.1, data_11_820.2]

/-- Complete interval computation for depth 11, residue 821. -/
theorem bounds_11_821 : exactInterval 11 821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_821 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 821) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_821 : oddCount 821 11 = 3 ∧ acceleratedOrbit 11 821 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_821 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 821) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_821.1, data_11_821.2]

/-- Complete interval computation for depth 11, residue 822. -/
theorem bounds_11_822 : exactInterval 11 822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_822 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 822) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_822 : oddCount 822 11 = 7 ∧ acceleratedOrbit 11 822 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_822 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 822) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_822.1, data_11_822.2]

/-- Complete interval computation for depth 11, residue 823. -/
theorem bounds_11_823 : exactInterval 11 823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_823 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 823) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_823 : oddCount 823 11 = 7 ∧ acceleratedOrbit 11 823 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_823 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 823) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_823.1, data_11_823.2]

/-- Complete interval computation for depth 11, residue 824. -/
theorem bounds_11_824 : exactInterval 11 824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_824 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 824) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_824 : oddCount 824 11 = 7 ∧ acceleratedOrbit 11 824 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_824 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 824) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_824.1, data_11_824.2]

/-- Complete interval computation for depth 11, residue 825. -/
theorem bounds_11_825 : exactInterval 11 825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_825 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 825) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_825 : oddCount 825 11 = 7 ∧ acceleratedOrbit 11 825 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_825 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 825) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_825.1, data_11_825.2]

/-- Complete interval computation for depth 11, residue 826. -/
theorem bounds_11_826 : exactInterval 11 826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_826 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 826) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_826 : oddCount 826 11 = 7 ∧ acceleratedOrbit 11 826 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_826 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 826) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_826.1, data_11_826.2]

/-- Complete interval computation for depth 11, residue 827. -/
theorem bounds_11_827 : exactInterval 11 827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_827 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 827) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_827 : oddCount 827 11 = 6 ∧ acceleratedOrbit 11 827 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_827 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 827) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_827.1, data_11_827.2]

/-- Complete interval computation for depth 11, residue 828. -/
theorem bounds_11_828 : exactInterval 11 828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_828 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 828) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_828 : oddCount 828 11 = 7 ∧ acceleratedOrbit 11 828 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_828 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 828) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_828.1, data_11_828.2]

/-- Complete interval computation for depth 11, residue 829. -/
theorem bounds_11_829 : exactInterval 11 829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_829 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 829) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_829 : oddCount 829 11 = 7 ∧ acceleratedOrbit 11 829 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_829 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 829) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_829.1, data_11_829.2]

/-- Complete interval computation for depth 11, residue 830. -/
theorem bounds_11_830 : exactInterval 11 830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_830 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 830) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_830 : oddCount 830 11 = 8 ∧ acceleratedOrbit 11 830 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_830 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 830) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_830.1, data_11_830.2]

/-- Complete interval computation for depth 11, residue 831. -/
theorem bounds_11_831 : exactInterval 11 831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_831 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 831) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_831 : oddCount 831 11 = 8 ∧ acceleratedOrbit 11 831 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_831 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 831) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_831.1, data_11_831.2]

/-- Complete interval computation for depth 11, residue 832. -/
theorem bounds_11_832 : exactInterval 11 832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_832 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 832) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_832 : oddCount 832 11 = 2 ∧ acceleratedOrbit 11 832 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_832 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 832) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_832.1, data_11_832.2]

/-- Complete interval computation for depth 11, residue 833. -/
theorem bounds_11_833 : exactInterval 11 833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_833 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 833) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_833 : oddCount 833 11 = 3 ∧ acceleratedOrbit 11 833 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_833 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 833) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_833.1, data_11_833.2]

end Collatz.Research.StoppingAtlas.Batch0121
