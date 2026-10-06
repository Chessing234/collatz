import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0122

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 834. -/
theorem bounds_11_834 : exactInterval 11 834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_834 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 834) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_834 : oddCount 834 11 = 6 ∧ acceleratedOrbit 11 834 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_834 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 834) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_834.1, data_11_834.2]

/-- Complete interval computation for depth 11, residue 835. -/
theorem bounds_11_835 : exactInterval 11 835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_835 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 835) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_835 : oddCount 835 11 = 6 ∧ acceleratedOrbit 11 835 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_835 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 835) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_835.1, data_11_835.2]

/-- Complete interval computation for depth 11, residue 836. -/
theorem bounds_11_836 : exactInterval 11 836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_836 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 836) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_836 : oddCount 836 11 = 5 ∧ acceleratedOrbit 11 836 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_836 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 836) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_836.1, data_11_836.2]

/-- Complete interval computation for depth 11, residue 837. -/
theorem bounds_11_837 : exactInterval 11 837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_837 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 837) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_837 : oddCount 837 11 = 5 ∧ acceleratedOrbit 11 837 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_837 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 837) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_837.1, data_11_837.2]

/-- Complete interval computation for depth 11, residue 838. -/
theorem bounds_11_838 : exactInterval 11 838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_838 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 838) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_838 : oddCount 838 11 = 5 ∧ acceleratedOrbit 11 838 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_838 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 838) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_838.1, data_11_838.2]

/-- Complete interval computation for depth 11, residue 839. -/
theorem bounds_11_839 : exactInterval 11 839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_839 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 839) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_839 : oddCount 839 11 = 8 ∧ acceleratedOrbit 11 839 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_839 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 839) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_839.1, data_11_839.2]

/-- Complete interval computation for depth 11, residue 840. -/
theorem bounds_11_840 : exactInterval 11 840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_840 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 840) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_840 : oddCount 840 11 = 5 ∧ acceleratedOrbit 11 840 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_840 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 840) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_840.1, data_11_840.2]

/-- Complete interval computation for depth 11, residue 841. -/
theorem bounds_11_841 : exactInterval 11 841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_841 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 841) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_841 : oddCount 841 11 = 5 ∧ acceleratedOrbit 11 841 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_841 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 841) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_841.1, data_11_841.2]

/-- Complete interval computation for depth 11, residue 842. -/
theorem bounds_11_842 : exactInterval 11 842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_842 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 842) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_842 : oddCount 842 11 = 5 ∧ acceleratedOrbit 11 842 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_842 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 842) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_842.1, data_11_842.2]

/-- Complete interval computation for depth 11, residue 843. -/
theorem bounds_11_843 : exactInterval 11 843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_843 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 843) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_843 : oddCount 843 11 = 5 ∧ acceleratedOrbit 11 843 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_843 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 843) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_843.1, data_11_843.2]

/-- Complete interval computation for depth 11, residue 844. -/
theorem bounds_11_844 : exactInterval 11 844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_844 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 844) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_844 : oddCount 844 11 = 5 ∧ acceleratedOrbit 11 844 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_844 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 844) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_844.1, data_11_844.2]

/-- Complete interval computation for depth 11, residue 845. -/
theorem bounds_11_845 : exactInterval 11 845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_845 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 845) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_845 : oddCount 845 11 = 5 ∧ acceleratedOrbit 11 845 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_845 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 845) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_845.1, data_11_845.2]

/-- Complete interval computation for depth 11, residue 846. -/
theorem bounds_11_846 : exactInterval 11 846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_846 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 846) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_846 : oddCount 846 11 = 6 ∧ acceleratedOrbit 11 846 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_846 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 846) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_846.1, data_11_846.2]

/-- Complete interval computation for depth 11, residue 847. -/
theorem bounds_11_847 : exactInterval 11 847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_847 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 847) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_847 : oddCount 847 11 = 6 ∧ acceleratedOrbit 11 847 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_847 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 847) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_847.1, data_11_847.2]

/-- Complete interval computation for depth 11, residue 848. -/
theorem bounds_11_848 : exactInterval 11 848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_848 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 848) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_848 : oddCount 848 11 = 2 ∧ acceleratedOrbit 11 848 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_848 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 848) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_848.1, data_11_848.2]

end Collatz.Research.StoppingAtlas.Batch0122
