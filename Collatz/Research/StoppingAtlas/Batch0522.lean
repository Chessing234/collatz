import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0522

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 834. -/
theorem bounds_13_834 : exactInterval 13 834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_834 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 834) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_834 : oddCount 834 13 = 8 ∧ acceleratedOrbit 13 834 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_834 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 834) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_834.1, data_13_834.2]

/-- Complete interval computation for depth 13, residue 835. -/
theorem bounds_13_835 : exactInterval 13 835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_835 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 835) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_835 : oddCount 835 13 = 8 ∧ acceleratedOrbit 13 835 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_835 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 835) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_835.1, data_13_835.2]

/-- Complete interval computation for depth 13, residue 836. -/
theorem bounds_13_836 : exactInterval 13 836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_836 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 836) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_836 : oddCount 836 13 = 6 ∧ acceleratedOrbit 13 836 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_836 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 836) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_836.1, data_13_836.2]

/-- Complete interval computation for depth 13, residue 837. -/
theorem bounds_13_837 : exactInterval 13 837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_837 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 837) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_837 : oddCount 837 13 = 6 ∧ acceleratedOrbit 13 837 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_837 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 837) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_837.1, data_13_837.2]

/-- Complete interval computation for depth 13, residue 838. -/
theorem bounds_13_838 : exactInterval 13 838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_838 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 838) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_838 : oddCount 838 13 = 6 ∧ acceleratedOrbit 13 838 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_838 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 838) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_838.1, data_13_838.2]

/-- Complete interval computation for depth 13, residue 839. -/
theorem bounds_13_839 : exactInterval 13 839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_839 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 839) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_839 : oddCount 839 13 = 9 ∧ acceleratedOrbit 13 839 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_839 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 839) = 3 ^ 9 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_839.1, data_13_839.2]

/-- Complete interval computation for depth 13, residue 840. -/
theorem bounds_13_840 : exactInterval 13 840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_840 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 840) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_840 : oddCount 840 13 = 6 ∧ acceleratedOrbit 13 840 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_840 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 840) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_840.1, data_13_840.2]

/-- Complete interval computation for depth 13, residue 841. -/
theorem bounds_13_841 : exactInterval 13 841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_841 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 841) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_841 : oddCount 841 13 = 5 ∧ acceleratedOrbit 13 841 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_841 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 841) = 3 ^ 5 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_841.1, data_13_841.2]

/-- Complete interval computation for depth 13, residue 842. -/
theorem bounds_13_842 : exactInterval 13 842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_842 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 842) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_842 : oddCount 842 13 = 6 ∧ acceleratedOrbit 13 842 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_842 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 842) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_842.1, data_13_842.2]

/-- Complete interval computation for depth 13, residue 843. -/
theorem bounds_13_843 : exactInterval 13 843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_843 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 843) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_843 : oddCount 843 13 = 6 ∧ acceleratedOrbit 13 843 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_843 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 843) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_843.1, data_13_843.2]

/-- Complete interval computation for depth 13, residue 844. -/
theorem bounds_13_844 : exactInterval 13 844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_844 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 844) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_844 : oddCount 844 13 = 6 ∧ acceleratedOrbit 13 844 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_844 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 844) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_844.1, data_13_844.2]

/-- Complete interval computation for depth 13, residue 845. -/
theorem bounds_13_845 : exactInterval 13 845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_845 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 845) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_845 : oddCount 845 13 = 6 ∧ acceleratedOrbit 13 845 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_845 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 845) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_845.1, data_13_845.2]

/-- Complete interval computation for depth 13, residue 846. -/
theorem bounds_13_846 : exactInterval 13 846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_846 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 846) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_846 : oddCount 846 13 = 7 ∧ acceleratedOrbit 13 846 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_846 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 846) = 3 ^ 7 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_846.1, data_13_846.2]

/-- Complete interval computation for depth 13, residue 847. -/
theorem bounds_13_847 : exactInterval 13 847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_847 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 847) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_847 : oddCount 847 13 = 7 ∧ acceleratedOrbit 13 847 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_847 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 847) = 3 ^ 7 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_847.1, data_13_847.2]

/-- Complete interval computation for depth 13, residue 848. -/
theorem bounds_13_848 : exactInterval 13 848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_848 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 848) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_848 : oddCount 848 13 = 2 ∧ acceleratedOrbit 13 848 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_848 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 848) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_848.1, data_13_848.2]

end Collatz.Research.StoppingAtlas.Batch0522
