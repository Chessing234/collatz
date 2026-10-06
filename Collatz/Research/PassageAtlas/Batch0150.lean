import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0150

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4882. -/
theorem bounds_15_4882 : exactInterval 15 4882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4882 : oddCount 4882 15 = 9 ∧ acceleratedOrbit 15 4882 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4882) = 3 ^ 9 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4882.1, data_15_4882.2]

/-- Complete interval computation for depth 15, residue 4883. -/
theorem bounds_15_4883 : exactInterval 15 4883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4883 : oddCount 4883 15 = 9 ∧ acceleratedOrbit 15 4883 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4883) = 3 ^ 9 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4883.1, data_15_4883.2]

/-- Complete interval computation for depth 15, residue 4884. -/
theorem bounds_15_4884 : exactInterval 15 4884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4884 : oddCount 4884 15 = 5 ∧ acceleratedOrbit 15 4884 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4884) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4884.1, data_15_4884.2]

/-- Complete interval computation for depth 15, residue 4885. -/
theorem bounds_15_4885 : exactInterval 15 4885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4885 : oddCount 4885 15 = 5 ∧ acceleratedOrbit 15 4885 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4885) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4885.1, data_15_4885.2]

/-- Complete interval computation for depth 15, residue 4886. -/
theorem bounds_15_4886 : exactInterval 15 4886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4886 : oddCount 4886 15 = 8 ∧ acceleratedOrbit 15 4886 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4886) = 3 ^ 8 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4886.1, data_15_4886.2]

/-- Complete interval computation for depth 15, residue 4887. -/
theorem bounds_15_4887 : exactInterval 15 4887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4887 : oddCount 4887 15 = 8 ∧ acceleratedOrbit 15 4887 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4887) = 3 ^ 8 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4887.1, data_15_4887.2]

/-- Complete interval computation for depth 15, residue 4888. -/
theorem bounds_15_4888 : exactInterval 15 4888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4888 : oddCount 4888 15 = 5 ∧ acceleratedOrbit 15 4888 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4888) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4888.1, data_15_4888.2]

/-- Complete interval computation for depth 15, residue 4889. -/
theorem bounds_15_4889 : exactInterval 15 4889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4889 : oddCount 4889 15 = 8 ∧ acceleratedOrbit 15 4889 = 980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4889) = 3 ^ 8 * m + 980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4889.1, data_15_4889.2]

/-- Complete interval computation for depth 15, residue 4890. -/
theorem bounds_15_4890 : exactInterval 15 4890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4890 : oddCount 4890 15 = 5 ∧ acceleratedOrbit 15 4890 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4890) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4890.1, data_15_4890.2]

/-- Complete interval computation for depth 15, residue 4891. -/
theorem bounds_15_4891 : exactInterval 15 4891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4891 : oddCount 4891 15 = 11 ∧ acceleratedOrbit 15 4891 = 26450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4891) = 3 ^ 11 * m + 26450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4891.1, data_15_4891.2]

/-- Complete interval computation for depth 15, residue 4892. -/
theorem bounds_15_4892 : exactInterval 15 4892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4892 : oddCount 4892 15 = 6 ∧ acceleratedOrbit 15 4892 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4892) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4892.1, data_15_4892.2]

/-- Complete interval computation for depth 15, residue 4893. -/
theorem bounds_15_4893 : exactInterval 15 4893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4893 : oddCount 4893 15 = 6 ∧ acceleratedOrbit 15 4893 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4893) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4893.1, data_15_4893.2]

/-- Complete interval computation for depth 15, residue 4894. -/
theorem bounds_15_4894 : exactInterval 15 4894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4894 : oddCount 4894 15 = 6 ∧ acceleratedOrbit 15 4894 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4894) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4894.1, data_15_4894.2]

/-- Complete interval computation for depth 15, residue 4895. -/
theorem bounds_15_4895 : exactInterval 15 4895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4895 : oddCount 4895 15 = 10 ∧ acceleratedOrbit 15 4895 = 8824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4895) = 3 ^ 10 * m + 8824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4895.1, data_15_4895.2]

/-- Complete interval computation for depth 15, residue 4896. -/
theorem bounds_15_4896 : exactInterval 15 4896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4896 : oddCount 4896 15 = 5 ∧ acceleratedOrbit 15 4896 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4896) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4896.1, data_15_4896.2]

/-- Complete interval computation for depth 15, residue 4897. -/
theorem bounds_15_4897 : exactInterval 15 4897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4897 : oddCount 4897 15 = 8 ∧ acceleratedOrbit 15 4897 = 982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4897) = 3 ^ 8 * m + 982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4897.1, data_15_4897.2]

/-- Complete interval computation for depth 15, residue 4898. -/
theorem bounds_15_4898 : exactInterval 15 4898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4898 : oddCount 4898 15 = 6 ∧ acceleratedOrbit 15 4898 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4898) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4898.1, data_15_4898.2]

/-- Complete interval computation for depth 15, residue 4899. -/
theorem bounds_15_4899 : exactInterval 15 4899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4899 : oddCount 4899 15 = 6 ∧ acceleratedOrbit 15 4899 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4899) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4899.1, data_15_4899.2]

/-- Complete interval computation for depth 15, residue 4900. -/
theorem bounds_15_4900 : exactInterval 15 4900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4900 : oddCount 4900 15 = 6 ∧ acceleratedOrbit 15 4900 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4900) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4900.1, data_15_4900.2]

/-- Complete interval computation for depth 15, residue 4901. -/
theorem bounds_15_4901 : exactInterval 15 4901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4901 : oddCount 4901 15 = 6 ∧ acceleratedOrbit 15 4901 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4901) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4901.1, data_15_4901.2]

/-- Complete interval computation for depth 15, residue 4902. -/
theorem bounds_15_4902 : exactInterval 15 4902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4902 : oddCount 4902 15 = 6 ∧ acceleratedOrbit 15 4902 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4902) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4902.1, data_15_4902.2]

/-- Complete interval computation for depth 15, residue 4903. -/
theorem bounds_15_4903 : exactInterval 15 4903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4903 : oddCount 4903 15 = 10 ∧ acceleratedOrbit 15 4903 = 8839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4903) = 3 ^ 10 * m + 8839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4903.1, data_15_4903.2]

/-- Complete interval computation for depth 15, residue 4904. -/
theorem bounds_15_4904 : exactInterval 15 4904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4904 : oddCount 4904 15 = 5 ∧ acceleratedOrbit 15 4904 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4904) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4904.1, data_15_4904.2]

/-- Complete interval computation for depth 15, residue 4905. -/
theorem bounds_15_4905 : exactInterval 15 4905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4905 : oddCount 4905 15 = 8 ∧ acceleratedOrbit 15 4905 = 983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4905) = 3 ^ 8 * m + 983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4905.1, data_15_4905.2]

/-- Complete interval computation for depth 15, residue 4906. -/
theorem bounds_15_4906 : exactInterval 15 4906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4906 : oddCount 4906 15 = 5 ∧ acceleratedOrbit 15 4906 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4906) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4906.1, data_15_4906.2]

/-- Complete interval computation for depth 15, residue 4907. -/
theorem bounds_15_4907 : exactInterval 15 4907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4907 : oddCount 4907 15 = 7 ∧ acceleratedOrbit 15 4907 = 328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4907) = 3 ^ 7 * m + 328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4907.1, data_15_4907.2]

/-- Complete interval computation for depth 15, residue 4908. -/
theorem bounds_15_4908 : exactInterval 15 4908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4908 : oddCount 4908 15 = 6 ∧ acceleratedOrbit 15 4908 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4908) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4908.1, data_15_4908.2]

/-- Complete interval computation for depth 15, residue 4909. -/
theorem bounds_15_4909 : exactInterval 15 4909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4909 : oddCount 4909 15 = 6 ∧ acceleratedOrbit 15 4909 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4909) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4909.1, data_15_4909.2]

/-- Complete interval computation for depth 15, residue 4910. -/
theorem bounds_15_4910 : exactInterval 15 4910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4910 : oddCount 4910 15 = 6 ∧ acceleratedOrbit 15 4910 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4910) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4910.1, data_15_4910.2]

/-- Complete interval computation for depth 15, residue 4911. -/
theorem bounds_15_4911 : exactInterval 15 4911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4911 : oddCount 4911 15 = 10 ∧ acceleratedOrbit 15 4911 = 8855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4911) = 3 ^ 10 * m + 8855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4911.1, data_15_4911.2]

/-- Complete interval computation for depth 15, residue 4912. -/
theorem bounds_15_4912 : exactInterval 15 4912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4912 : oddCount 4912 15 = 5 ∧ acceleratedOrbit 15 4912 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4912) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4912.1, data_15_4912.2]

/-- Complete interval computation for depth 15, residue 4913. -/
theorem bounds_15_4913 : exactInterval 15 4913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4913 : oddCount 4913 15 = 6 ∧ acceleratedOrbit 15 4913 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4913) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4913.1, data_15_4913.2]

/-- Complete interval computation for depth 15, residue 4914. -/
theorem bounds_15_4914 : exactInterval 15 4914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4914 : oddCount 4914 15 = 6 ∧ acceleratedOrbit 15 4914 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4914) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4914.1, data_15_4914.2]

end Collatz.Research.PassageAtlas.Batch0150
