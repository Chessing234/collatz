import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0255

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 829. -/
theorem bounds_12_829 : exactInterval 12 829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_829 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 829) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_829 : oddCount 829 12 = 7 ∧ acceleratedOrbit 12 829 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_829 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 829) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_829.1, data_12_829.2]

/-- Complete interval computation for depth 12, residue 830. -/
theorem bounds_12_830 : exactInterval 12 830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_830 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 830) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_830 : oddCount 830 12 = 8 ∧ acceleratedOrbit 12 830 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_830 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 830) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_830.1, data_12_830.2]

/-- Complete interval computation for depth 12, residue 831. -/
theorem bounds_12_831 : exactInterval 12 831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_831 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 831) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_831 : oddCount 831 12 = 8 ∧ acceleratedOrbit 12 831 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_831 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 831) = 3 ^ 8 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_831.1, data_12_831.2]

/-- Complete interval computation for depth 12, residue 832. -/
theorem bounds_12_832 : exactInterval 12 832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_832 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 832) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_832 : oddCount 832 12 = 2 ∧ acceleratedOrbit 12 832 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_832 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 832) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_832.1, data_12_832.2]

/-- Complete interval computation for depth 12, residue 833. -/
theorem bounds_12_833 : exactInterval 12 833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_833 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 833) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_833 : oddCount 833 12 = 4 ∧ acceleratedOrbit 12 833 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_833 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 833) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_833.1, data_12_833.2]

/-- Complete interval computation for depth 12, residue 834. -/
theorem bounds_12_834 : exactInterval 12 834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_834 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 834) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_834 : oddCount 834 12 = 7 ∧ acceleratedOrbit 12 834 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_834 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 834) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_834.1, data_12_834.2]

/-- Complete interval computation for depth 12, residue 835. -/
theorem bounds_12_835 : exactInterval 12 835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_835 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 835) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_835 : oddCount 835 12 = 7 ∧ acceleratedOrbit 12 835 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_835 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 835) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_835.1, data_12_835.2]

/-- Complete interval computation for depth 12, residue 836. -/
theorem bounds_12_836 : exactInterval 12 836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_836 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 836) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_836 : oddCount 836 12 = 6 ∧ acceleratedOrbit 12 836 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_836 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 836) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_836.1, data_12_836.2]

/-- Complete interval computation for depth 12, residue 837. -/
theorem bounds_12_837 : exactInterval 12 837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_837 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 837) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_837 : oddCount 837 12 = 6 ∧ acceleratedOrbit 12 837 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_837 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 837) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_837.1, data_12_837.2]

/-- Complete interval computation for depth 12, residue 838. -/
theorem bounds_12_838 : exactInterval 12 838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_838 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 838) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_838 : oddCount 838 12 = 6 ∧ acceleratedOrbit 12 838 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_838 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 838) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_838.1, data_12_838.2]

/-- Complete interval computation for depth 12, residue 839. -/
theorem bounds_12_839 : exactInterval 12 839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_839 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 839) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_839 : oddCount 839 12 = 9 ∧ acceleratedOrbit 12 839 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_839 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 839) = 3 ^ 9 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_839.1, data_12_839.2]

/-- Complete interval computation for depth 12, residue 840. -/
theorem bounds_12_840 : exactInterval 12 840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_840 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 840) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_840 : oddCount 840 12 = 6 ∧ acceleratedOrbit 12 840 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_840 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 840) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_840.1, data_12_840.2]

/-- Complete interval computation for depth 12, residue 841. -/
theorem bounds_12_841 : exactInterval 12 841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_841 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 841) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_841 : oddCount 841 12 = 5 ∧ acceleratedOrbit 12 841 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_841 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 841) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_841.1, data_12_841.2]

/-- Complete interval computation for depth 12, residue 842. -/
theorem bounds_12_842 : exactInterval 12 842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_842 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 842) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_842 : oddCount 842 12 = 6 ∧ acceleratedOrbit 12 842 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_842 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 842) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_842.1, data_12_842.2]

/-- Complete interval computation for depth 12, residue 843. -/
theorem bounds_12_843 : exactInterval 12 843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_843 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 843) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_843 : oddCount 843 12 = 6 ∧ acceleratedOrbit 12 843 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_843 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 843) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_843.1, data_12_843.2]

end Collatz.Research.StoppingAtlas.Batch0255
