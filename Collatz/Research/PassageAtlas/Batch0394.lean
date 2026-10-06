import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0394

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12877. -/
theorem bounds_15_12877 : exactInterval 15 12877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12877 : oddCount 12877 15 = 8 ∧ acceleratedOrbit 15 12877 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12877) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12877.1, data_15_12877.2]

/-- Complete interval computation for depth 15, residue 12878. -/
theorem bounds_15_12878 : exactInterval 15 12878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12878 : oddCount 12878 15 = 9 ∧ acceleratedOrbit 15 12878 = 7739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12878) = 3 ^ 9 * m + 7739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12878.1, data_15_12878.2]

/-- Complete interval computation for depth 15, residue 12879. -/
theorem bounds_15_12879 : exactInterval 15 12879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12879 : oddCount 12879 15 = 9 ∧ acceleratedOrbit 15 12879 = 7739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12879) = 3 ^ 9 * m + 7739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12879.1, data_15_12879.2]

/-- Complete interval computation for depth 15, residue 12880. -/
theorem bounds_15_12880 : exactInterval 15 12880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12880 : oddCount 12880 15 = 4 ∧ acceleratedOrbit 15 12880 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12880) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12880.1, data_15_12880.2]

/-- Complete interval computation for depth 15, residue 12881. -/
theorem bounds_15_12881 : exactInterval 15 12881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12881 : oddCount 12881 15 = 7 ∧ acceleratedOrbit 15 12881 = 860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12881) = 3 ^ 7 * m + 860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12881.1, data_15_12881.2]

/-- Complete interval computation for depth 15, residue 12882. -/
theorem bounds_15_12882 : exactInterval 15 12882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12882 : oddCount 12882 15 = 7 ∧ acceleratedOrbit 15 12882 = 860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12882) = 3 ^ 7 * m + 860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12882.1, data_15_12882.2]

/-- Complete interval computation for depth 15, residue 12883. -/
theorem bounds_15_12883 : exactInterval 15 12883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12883 : oddCount 12883 15 = 7 ∧ acceleratedOrbit 15 12883 = 860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12883) = 3 ^ 7 * m + 860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12883.1, data_15_12883.2]

/-- Complete interval computation for depth 15, residue 12884. -/
theorem bounds_15_12884 : exactInterval 15 12884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12884 : oddCount 12884 15 = 4 ∧ acceleratedOrbit 15 12884 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12884) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12884.1, data_15_12884.2]

/-- Complete interval computation for depth 15, residue 12885. -/
theorem bounds_15_12885 : exactInterval 15 12885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12885 : oddCount 12885 15 = 4 ∧ acceleratedOrbit 15 12885 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12885) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12885.1, data_15_12885.2]

/-- Complete interval computation for depth 15, residue 12886. -/
theorem bounds_15_12886 : exactInterval 15 12886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12886 : oddCount 12886 15 = 8 ∧ acceleratedOrbit 15 12886 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12886) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12886.1, data_15_12886.2]

/-- Complete interval computation for depth 15, residue 12887. -/
theorem bounds_15_12887 : exactInterval 15 12887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12887 : oddCount 12887 15 = 8 ∧ acceleratedOrbit 15 12887 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12887) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12887.1, data_15_12887.2]

/-- Complete interval computation for depth 15, residue 12888. -/
theorem bounds_15_12888 : exactInterval 15 12888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12888 : oddCount 12888 15 = 4 ∧ acceleratedOrbit 15 12888 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12888) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12888.1, data_15_12888.2]

/-- Complete interval computation for depth 15, residue 12889. -/
theorem bounds_15_12889 : exactInterval 15 12889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12889 : oddCount 12889 15 = 10 ∧ acceleratedOrbit 15 12889 = 23237 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12889) = 3 ^ 10 * m + 23237 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12889.1, data_15_12889.2]

/-- Complete interval computation for depth 15, residue 12890. -/
theorem bounds_15_12890 : exactInterval 15 12890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12890 : oddCount 12890 15 = 4 ∧ acceleratedOrbit 15 12890 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12890) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12890.1, data_15_12890.2]

/-- Complete interval computation for depth 15, residue 12891. -/
theorem bounds_15_12891 : exactInterval 15 12891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12891 : oddCount 12891 15 = 11 ∧ acceleratedOrbit 15 12891 = 69700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12891) = 3 ^ 11 * m + 69700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12891.1, data_15_12891.2]

/-- Complete interval computation for depth 15, residue 12892. -/
theorem bounds_15_12892 : exactInterval 15 12892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12892 : oddCount 12892 15 = 4 ∧ acceleratedOrbit 15 12892 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12892) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12892.1, data_15_12892.2]

/-- Complete interval computation for depth 15, residue 12893. -/
theorem bounds_15_12893 : exactInterval 15 12893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12893 : oddCount 12893 15 = 4 ∧ acceleratedOrbit 15 12893 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12893) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12893.1, data_15_12893.2]

/-- Complete interval computation for depth 15, residue 12894. -/
theorem bounds_15_12894 : exactInterval 15 12894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12894 : oddCount 12894 15 = 9 ∧ acceleratedOrbit 15 12894 = 7748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12894) = 3 ^ 9 * m + 7748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12894.1, data_15_12894.2]

/-- Complete interval computation for depth 15, residue 12895. -/
theorem bounds_15_12895 : exactInterval 15 12895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12895 : oddCount 12895 15 = 9 ∧ acceleratedOrbit 15 12895 = 7748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12895) = 3 ^ 9 * m + 7748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12895.1, data_15_12895.2]

/-- Complete interval computation for depth 15, residue 12896. -/
theorem bounds_15_12896 : exactInterval 15 12896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12896 : oddCount 12896 15 = 4 ∧ acceleratedOrbit 15 12896 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12896) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12896.1, data_15_12896.2]

/-- Complete interval computation for depth 15, residue 12897. -/
theorem bounds_15_12897 : exactInterval 15 12897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12897 : oddCount 12897 15 = 6 ∧ acceleratedOrbit 15 12897 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12897) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12897.1, data_15_12897.2]

/-- Complete interval computation for depth 15, residue 12898. -/
theorem bounds_15_12898 : exactInterval 15 12898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12898 : oddCount 12898 15 = 7 ∧ acceleratedOrbit 15 12898 = 863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12898) = 3 ^ 7 * m + 863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12898.1, data_15_12898.2]

/-- Complete interval computation for depth 15, residue 12899. -/
theorem bounds_15_12899 : exactInterval 15 12899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12899 : oddCount 12899 15 = 7 ∧ acceleratedOrbit 15 12899 = 863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12899) = 3 ^ 7 * m + 863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12899.1, data_15_12899.2]

/-- Complete interval computation for depth 15, residue 12900. -/
theorem bounds_15_12900 : exactInterval 15 12900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12900 : oddCount 12900 15 = 7 ∧ acceleratedOrbit 15 12900 = 863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12900) = 3 ^ 7 * m + 863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12900.1, data_15_12900.2]

/-- Complete interval computation for depth 15, residue 12901. -/
theorem bounds_15_12901 : exactInterval 15 12901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12901 : oddCount 12901 15 = 7 ∧ acceleratedOrbit 15 12901 = 863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12901) = 3 ^ 7 * m + 863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12901.1, data_15_12901.2]

/-- Complete interval computation for depth 15, residue 12902. -/
theorem bounds_15_12902 : exactInterval 15 12902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12902 : oddCount 12902 15 = 7 ∧ acceleratedOrbit 15 12902 = 863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12902) = 3 ^ 7 * m + 863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12902.1, data_15_12902.2]

/-- Complete interval computation for depth 15, residue 12903. -/
theorem bounds_15_12903 : exactInterval 15 12903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12903 : oddCount 12903 15 = 8 ∧ acceleratedOrbit 15 12903 = 2584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12903) = 3 ^ 8 * m + 2584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12903.1, data_15_12903.2]

/-- Complete interval computation for depth 15, residue 12904. -/
theorem bounds_15_12904 : exactInterval 15 12904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12904 : oddCount 12904 15 = 4 ∧ acceleratedOrbit 15 12904 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12904) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12904.1, data_15_12904.2]

/-- Complete interval computation for depth 15, residue 12905. -/
theorem bounds_15_12905 : exactInterval 15 12905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12905 : oddCount 12905 15 = 10 ∧ acceleratedOrbit 15 12905 = 23260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12905) = 3 ^ 10 * m + 23260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12905.1, data_15_12905.2]

/-- Complete interval computation for depth 15, residue 12906. -/
theorem bounds_15_12906 : exactInterval 15 12906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12906 : oddCount 12906 15 = 4 ∧ acceleratedOrbit 15 12906 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12906) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12906.1, data_15_12906.2]

/-- Complete interval computation for depth 15, residue 12907. -/
theorem bounds_15_12907 : exactInterval 15 12907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12907 : oddCount 12907 15 = 8 ∧ acceleratedOrbit 15 12907 = 2585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12907) = 3 ^ 8 * m + 2585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12907.1, data_15_12907.2]

/-- Complete interval computation for depth 15, residue 12908. -/
theorem bounds_15_12908 : exactInterval 15 12908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12908 : oddCount 12908 15 = 10 ∧ acceleratedOrbit 15 12908 = 23273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12908) = 3 ^ 10 * m + 23273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12908.1, data_15_12908.2]

/-- Complete interval computation for depth 15, residue 12909. -/
theorem bounds_15_12909 : exactInterval 15 12909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12909 : oddCount 12909 15 = 10 ∧ acceleratedOrbit 15 12909 = 23273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12909) = 3 ^ 10 * m + 23273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12909.1, data_15_12909.2]

end Collatz.Research.PassageAtlas.Batch0394
