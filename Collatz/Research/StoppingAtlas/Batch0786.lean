import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0786

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4889. -/
theorem bounds_13_4889 : exactInterval 13 4889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4889 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4889) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4889 : oddCount 4889 13 = 7 ∧ acceleratedOrbit 13 4889 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4889 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4889) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4889.1, data_13_4889.2]

/-- Complete interval computation for depth 13, residue 4890. -/
theorem bounds_13_4890 : exactInterval 13 4890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4890 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4890) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4890 : oddCount 4890 13 = 4 ∧ acceleratedOrbit 13 4890 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4890 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4890) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4890.1, data_13_4890.2]

/-- Complete interval computation for depth 13, residue 4891. -/
theorem bounds_13_4891 : exactInterval 13 4891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4891 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4891) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4891 : oddCount 4891 13 = 9 ∧ acceleratedOrbit 13 4891 = 11755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4891 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4891) = 3 ^ 9 * m + 11755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4891.1, data_13_4891.2]

/-- Complete interval computation for depth 13, residue 4892. -/
theorem bounds_13_4892 : exactInterval 13 4892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4892 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4892) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4892 : oddCount 4892 13 = 6 ∧ acceleratedOrbit 13 4892 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4892 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4892) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4892.1, data_13_4892.2]

/-- Complete interval computation for depth 13, residue 4893. -/
theorem bounds_13_4893 : exactInterval 13 4893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4893 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4893) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4893 : oddCount 4893 13 = 6 ∧ acceleratedOrbit 13 4893 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4893 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4893) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4893.1, data_13_4893.2]

/-- Complete interval computation for depth 13, residue 4894. -/
theorem bounds_13_4894 : exactInterval 13 4894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4894 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4894) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4894 : oddCount 4894 13 = 6 ∧ acceleratedOrbit 13 4894 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4894 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4894) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4894.1, data_13_4894.2]

/-- Complete interval computation for depth 13, residue 4895. -/
theorem bounds_13_4895 : exactInterval 13 4895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4895 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4895) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4895 : oddCount 4895 13 = 9 ∧ acceleratedOrbit 13 4895 = 11765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4895 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4895) = 3 ^ 9 * m + 11765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4895.1, data_13_4895.2]

/-- Complete interval computation for depth 13, residue 4896. -/
theorem bounds_13_4896 : exactInterval 13 4896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4896 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4896) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4896 : oddCount 4896 13 = 4 ∧ acceleratedOrbit 13 4896 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4896 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4896) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4896.1, data_13_4896.2]

/-- Complete interval computation for depth 13, residue 4897. -/
theorem bounds_13_4897 : exactInterval 13 4897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4897 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4897) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4897 : oddCount 4897 13 = 7 ∧ acceleratedOrbit 13 4897 = 1309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4897 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4897) = 3 ^ 7 * m + 1309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4897.1, data_13_4897.2]

/-- Complete interval computation for depth 13, residue 4898. -/
theorem bounds_13_4898 : exactInterval 13 4898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4898 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4898) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4898 : oddCount 4898 13 = 5 ∧ acceleratedOrbit 13 4898 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4898 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4898) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4898.1, data_13_4898.2]

/-- Complete interval computation for depth 13, residue 4899. -/
theorem bounds_13_4899 : exactInterval 13 4899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4899 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4899) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4899 : oddCount 4899 13 = 5 ∧ acceleratedOrbit 13 4899 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4899 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4899) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4899.1, data_13_4899.2]

/-- Complete interval computation for depth 13, residue 4900. -/
theorem bounds_13_4900 : exactInterval 13 4900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4900 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4900) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4900 : oddCount 4900 13 = 5 ∧ acceleratedOrbit 13 4900 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4900 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4900) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4900.1, data_13_4900.2]

/-- Complete interval computation for depth 13, residue 4901. -/
theorem bounds_13_4901 : exactInterval 13 4901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4901 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4901) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4901 : oddCount 4901 13 = 5 ∧ acceleratedOrbit 13 4901 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4901 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4901) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4901.1, data_13_4901.2]

/-- Complete interval computation for depth 13, residue 4902. -/
theorem bounds_13_4902 : exactInterval 13 4902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4902 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4902) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4902 : oddCount 4902 13 = 5 ∧ acceleratedOrbit 13 4902 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4902 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4902) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4902.1, data_13_4902.2]

/-- Complete interval computation for depth 13, residue 4903. -/
theorem bounds_13_4903 : exactInterval 13 4903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4903 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4903) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4903 : oddCount 4903 13 = 9 ∧ acceleratedOrbit 13 4903 = 11785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4903 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4903) = 3 ^ 9 * m + 11785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4903.1, data_13_4903.2]

end Collatz.Research.StoppingAtlas.Batch0786
