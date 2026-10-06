import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0272

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8880. -/
theorem bounds_15_8880 : exactInterval 15 8880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8880 : oddCount 8880 15 = 4 ∧ acceleratedOrbit 15 8880 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8880) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8880.1, data_15_8880.2]

/-- Complete interval computation for depth 15, residue 8881. -/
theorem bounds_15_8881 : exactInterval 15 8881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8881 : oddCount 8881 15 = 9 ∧ acceleratedOrbit 15 8881 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8881) = 3 ^ 9 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8881.1, data_15_8881.2]

/-- Complete interval computation for depth 15, residue 8882. -/
theorem bounds_15_8882 : exactInterval 15 8882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8882 : oddCount 8882 15 = 9 ∧ acceleratedOrbit 15 8882 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8882) = 3 ^ 9 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8882.1, data_15_8882.2]

/-- Complete interval computation for depth 15, residue 8883. -/
theorem bounds_15_8883 : exactInterval 15 8883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8883 : oddCount 8883 15 = 9 ∧ acceleratedOrbit 15 8883 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8883) = 3 ^ 9 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8883.1, data_15_8883.2]

/-- Complete interval computation for depth 15, residue 8884. -/
theorem bounds_15_8884 : exactInterval 15 8884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8884 : oddCount 8884 15 = 4 ∧ acceleratedOrbit 15 8884 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8884) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8884.1, data_15_8884.2]

/-- Complete interval computation for depth 15, residue 8885. -/
theorem bounds_15_8885 : exactInterval 15 8885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8885 : oddCount 8885 15 = 4 ∧ acceleratedOrbit 15 8885 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8885) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8885.1, data_15_8885.2]

/-- Complete interval computation for depth 15, residue 8886. -/
theorem bounds_15_8886 : exactInterval 15 8886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8886 : oddCount 8886 15 = 8 ∧ acceleratedOrbit 15 8886 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8886) = 3 ^ 8 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8886.1, data_15_8886.2]

/-- Complete interval computation for depth 15, residue 8887. -/
theorem bounds_15_8887 : exactInterval 15 8887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8887 : oddCount 8887 15 = 8 ∧ acceleratedOrbit 15 8887 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8887) = 3 ^ 8 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8887.1, data_15_8887.2]

/-- Complete interval computation for depth 15, residue 8888. -/
theorem bounds_15_8888 : exactInterval 15 8888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8888 : oddCount 8888 15 = 4 ∧ acceleratedOrbit 15 8888 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8888) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8888.1, data_15_8888.2]

/-- Complete interval computation for depth 15, residue 8889. -/
theorem bounds_15_8889 : exactInterval 15 8889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8889 : oddCount 8889 15 = 9 ∧ acceleratedOrbit 15 8889 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8889) = 3 ^ 9 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8889.1, data_15_8889.2]

/-- Complete interval computation for depth 15, residue 8890. -/
theorem bounds_15_8890 : exactInterval 15 8890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8890 : oddCount 8890 15 = 4 ∧ acceleratedOrbit 15 8890 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8890) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8890.1, data_15_8890.2]

/-- Complete interval computation for depth 15, residue 8891. -/
theorem bounds_15_8891 : exactInterval 15 8891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8891 : oddCount 8891 15 = 10 ∧ acceleratedOrbit 15 8891 = 16028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8891) = 3 ^ 10 * m + 16028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8891.1, data_15_8891.2]

/-- Complete interval computation for depth 15, residue 8892. -/
theorem bounds_15_8892 : exactInterval 15 8892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8892 : oddCount 8892 15 = 10 ∧ acceleratedOrbit 15 8892 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8892) = 3 ^ 10 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8892.1, data_15_8892.2]

/-- Complete interval computation for depth 15, residue 8893. -/
theorem bounds_15_8893 : exactInterval 15 8893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8893 : oddCount 8893 15 = 10 ∧ acceleratedOrbit 15 8893 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8893) = 3 ^ 10 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8893.1, data_15_8893.2]

/-- Complete interval computation for depth 15, residue 8894. -/
theorem bounds_15_8894 : exactInterval 15 8894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8894 : oddCount 8894 15 = 10 ∧ acceleratedOrbit 15 8894 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8894) = 3 ^ 10 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8894.1, data_15_8894.2]

/-- Complete interval computation for depth 15, residue 8895. -/
theorem bounds_15_8895 : exactInterval 15 8895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8895 : oddCount 8895 15 = 12 ∧ acceleratedOrbit 15 8895 = 144281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8895) = 3 ^ 12 * m + 144281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8895.1, data_15_8895.2]

/-- Complete interval computation for depth 15, residue 8896. -/
theorem bounds_15_8896 : exactInterval 15 8896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8896 : oddCount 8896 15 = 5 ∧ acceleratedOrbit 15 8896 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8896) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8896.1, data_15_8896.2]

/-- Complete interval computation for depth 15, residue 8897. -/
theorem bounds_15_8897 : exactInterval 15 8897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8897 : oddCount 8897 15 = 4 ∧ acceleratedOrbit 15 8897 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8897) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8897.1, data_15_8897.2]

/-- Complete interval computation for depth 15, residue 8898. -/
theorem bounds_15_8898 : exactInterval 15 8898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8898 : oddCount 8898 15 = 8 ∧ acceleratedOrbit 15 8898 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8898) = 3 ^ 8 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8898.1, data_15_8898.2]

/-- Complete interval computation for depth 15, residue 8899. -/
theorem bounds_15_8899 : exactInterval 15 8899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8899 : oddCount 8899 15 = 8 ∧ acceleratedOrbit 15 8899 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8899) = 3 ^ 8 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8899.1, data_15_8899.2]

/-- Complete interval computation for depth 15, residue 8900. -/
theorem bounds_15_8900 : exactInterval 15 8900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8900 : oddCount 8900 15 = 6 ∧ acceleratedOrbit 15 8900 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8900) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8900.1, data_15_8900.2]

/-- Complete interval computation for depth 15, residue 8901. -/
theorem bounds_15_8901 : exactInterval 15 8901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8901 : oddCount 8901 15 = 6 ∧ acceleratedOrbit 15 8901 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8901) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8901.1, data_15_8901.2]

/-- Complete interval computation for depth 15, residue 8902. -/
theorem bounds_15_8902 : exactInterval 15 8902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8902 : oddCount 8902 15 = 6 ∧ acceleratedOrbit 15 8902 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8902) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8902.1, data_15_8902.2]

/-- Complete interval computation for depth 15, residue 8903. -/
theorem bounds_15_8903 : exactInterval 15 8903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8903 : oddCount 8903 15 = 8 ∧ acceleratedOrbit 15 8903 = 1784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8903) = 3 ^ 8 * m + 1784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8903.1, data_15_8903.2]

/-- Complete interval computation for depth 15, residue 8904. -/
theorem bounds_15_8904 : exactInterval 15 8904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8904 : oddCount 8904 15 = 6 ∧ acceleratedOrbit 15 8904 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8904) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8904.1, data_15_8904.2]

/-- Complete interval computation for depth 15, residue 8905. -/
theorem bounds_15_8905 : exactInterval 15 8905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8905 : oddCount 8905 15 = 7 ∧ acceleratedOrbit 15 8905 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8905) = 3 ^ 7 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8905.1, data_15_8905.2]

/-- Complete interval computation for depth 15, residue 8906. -/
theorem bounds_15_8906 : exactInterval 15 8906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8906 : oddCount 8906 15 = 6 ∧ acceleratedOrbit 15 8906 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8906) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8906.1, data_15_8906.2]

/-- Complete interval computation for depth 15, residue 8907. -/
theorem bounds_15_8907 : exactInterval 15 8907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8907 : oddCount 8907 15 = 7 ∧ acceleratedOrbit 15 8907 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8907) = 3 ^ 7 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8907.1, data_15_8907.2]

/-- Complete interval computation for depth 15, residue 8908. -/
theorem bounds_15_8908 : exactInterval 15 8908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8908 : oddCount 8908 15 = 6 ∧ acceleratedOrbit 15 8908 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8908) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8908.1, data_15_8908.2]

/-- Complete interval computation for depth 15, residue 8909. -/
theorem bounds_15_8909 : exactInterval 15 8909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8909 : oddCount 8909 15 = 6 ∧ acceleratedOrbit 15 8909 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8909) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8909.1, data_15_8909.2]

/-- Complete interval computation for depth 15, residue 8910. -/
theorem bounds_15_8910 : exactInterval 15 8910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8910 : oddCount 8910 15 = 9 ∧ acceleratedOrbit 15 8910 = 5354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8910) = 3 ^ 9 * m + 5354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8910.1, data_15_8910.2]

/-- Complete interval computation for depth 15, residue 8911. -/
theorem bounds_15_8911 : exactInterval 15 8911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8911 : oddCount 8911 15 = 9 ∧ acceleratedOrbit 15 8911 = 5354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8911) = 3 ^ 9 * m + 5354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8911.1, data_15_8911.2]

end Collatz.Research.PassageAtlas.Batch0272
