import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0055

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 829. -/
theorem bounds_10_829 : exactInterval 10 829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_829 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 829) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_829 : oddCount 829 10 = 6 ∧ acceleratedOrbit 10 829 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_829 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 829) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_829.1, data_10_829.2]

/-- Complete interval computation for depth 10, residue 830. -/
theorem bounds_10_830 : exactInterval 10 830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_830 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 830) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_830 : oddCount 830 10 = 7 ∧ acceleratedOrbit 10 830 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_830 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 830) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_830.1, data_10_830.2]

/-- Complete interval computation for depth 10, residue 831. -/
theorem bounds_10_831 : exactInterval 10 831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_831 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 831) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_831 : oddCount 831 10 = 7 ∧ acceleratedOrbit 10 831 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_831 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 831) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_831.1, data_10_831.2]

/-- Complete interval computation for depth 10, residue 832. -/
theorem bounds_10_832 : exactInterval 10 832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_832 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 832) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_832 : oddCount 832 10 = 2 ∧ acceleratedOrbit 10 832 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_832 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 832) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_832.1, data_10_832.2]

/-- Complete interval computation for depth 10, residue 833. -/
theorem bounds_10_833 : exactInterval 10 833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_833 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 833) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_833 : oddCount 833 10 = 3 ∧ acceleratedOrbit 10 833 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_833 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 833) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_833.1, data_10_833.2]

/-- Complete interval computation for depth 10, residue 834. -/
theorem bounds_10_834 : exactInterval 10 834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_834 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 834) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_834 : oddCount 834 10 = 5 ∧ acceleratedOrbit 10 834 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_834 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 834) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_834.1, data_10_834.2]

/-- Complete interval computation for depth 10, residue 835. -/
theorem bounds_10_835 : exactInterval 10 835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_835 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 835) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_835 : oddCount 835 10 = 5 ∧ acceleratedOrbit 10 835 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_835 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 835) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_835.1, data_10_835.2]

/-- Complete interval computation for depth 10, residue 836. -/
theorem bounds_10_836 : exactInterval 10 836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_836 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 836) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_836 : oddCount 836 10 = 4 ∧ acceleratedOrbit 10 836 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_836 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 836) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_836.1, data_10_836.2]

/-- Complete interval computation for depth 10, residue 837. -/
theorem bounds_10_837 : exactInterval 10 837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_837 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 837) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_837 : oddCount 837 10 = 4 ∧ acceleratedOrbit 10 837 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_837 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 837) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_837.1, data_10_837.2]

/-- Complete interval computation for depth 10, residue 838. -/
theorem bounds_10_838 : exactInterval 10 838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_838 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 838) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_838 : oddCount 838 10 = 4 ∧ acceleratedOrbit 10 838 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_838 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 838) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_838.1, data_10_838.2]

/-- Complete interval computation for depth 10, residue 839. -/
theorem bounds_10_839 : exactInterval 10 839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_839 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 839) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_839 : oddCount 839 10 = 7 ∧ acceleratedOrbit 10 839 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_839 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 839) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_839.1, data_10_839.2]

/-- Complete interval computation for depth 10, residue 840. -/
theorem bounds_10_840 : exactInterval 10 840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_840 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 840) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_840 : oddCount 840 10 = 5 ∧ acceleratedOrbit 10 840 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_840 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 840) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_840.1, data_10_840.2]

/-- Complete interval computation for depth 10, residue 841. -/
theorem bounds_10_841 : exactInterval 10 841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_841 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 841) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_841 : oddCount 841 10 = 5 ∧ acceleratedOrbit 10 841 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_841 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 841) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_841.1, data_10_841.2]

/-- Complete interval computation for depth 10, residue 842. -/
theorem bounds_10_842 : exactInterval 10 842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_842 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 842) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_842 : oddCount 842 10 = 5 ∧ acceleratedOrbit 10 842 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_842 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 842) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_842.1, data_10_842.2]

/-- Complete interval computation for depth 10, residue 843. -/
theorem bounds_10_843 : exactInterval 10 843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_843 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 843) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_843 : oddCount 843 10 = 4 ∧ acceleratedOrbit 10 843 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_843 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 843) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_843.1, data_10_843.2]

end Collatz.Research.StoppingAtlas.Batch0055
