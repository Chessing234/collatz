import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0577

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18874. -/
theorem bounds_15_18874 : exactInterval 15 18874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18874 : oddCount 18874 15 = 8 ∧ acceleratedOrbit 15 18874 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18874) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18874.1, data_15_18874.2]

/-- Complete interval computation for depth 15, residue 18875. -/
theorem bounds_15_18875 : exactInterval 15 18875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18875 : oddCount 18875 15 = 11 ∧ acceleratedOrbit 15 18875 = 102059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18875) = 3 ^ 11 * m + 102059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18875.1, data_15_18875.2]

/-- Complete interval computation for depth 15, residue 18876. -/
theorem bounds_15_18876 : exactInterval 15 18876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18876 : oddCount 18876 15 = 9 ∧ acceleratedOrbit 15 18876 = 11342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18876) = 3 ^ 9 * m + 11342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18876.1, data_15_18876.2]

/-- Complete interval computation for depth 15, residue 18877. -/
theorem bounds_15_18877 : exactInterval 15 18877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18877 : oddCount 18877 15 = 9 ∧ acceleratedOrbit 15 18877 = 11342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18877) = 3 ^ 9 * m + 11342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18877.1, data_15_18877.2]

/-- Complete interval computation for depth 15, residue 18878. -/
theorem bounds_15_18878 : exactInterval 15 18878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18878 : oddCount 18878 15 = 9 ∧ acceleratedOrbit 15 18878 = 11342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18878) = 3 ^ 9 * m + 11342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18878.1, data_15_18878.2]

/-- Complete interval computation for depth 15, residue 18879. -/
theorem bounds_15_18879 : exactInterval 15 18879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18879 : oddCount 18879 15 = 11 ∧ acceleratedOrbit 15 18879 = 102068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18879) = 3 ^ 11 * m + 102068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18879.1, data_15_18879.2]

/-- Complete interval computation for depth 15, residue 18880. -/
theorem bounds_15_18880 : exactInterval 15 18880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18880 : oddCount 18880 15 = 6 ∧ acceleratedOrbit 15 18880 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18880) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18880.1, data_15_18880.2]

/-- Complete interval computation for depth 15, residue 18881. -/
theorem bounds_15_18881 : exactInterval 15 18881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18881 : oddCount 18881 15 = 8 ∧ acceleratedOrbit 15 18881 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18881) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18881.1, data_15_18881.2]

/-- Complete interval computation for depth 15, residue 18882. -/
theorem bounds_15_18882 : exactInterval 15 18882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18882 : oddCount 18882 15 = 9 ∧ acceleratedOrbit 15 18882 = 11345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18882) = 3 ^ 9 * m + 11345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18882.1, data_15_18882.2]

/-- Complete interval computation for depth 15, residue 18883. -/
theorem bounds_15_18883 : exactInterval 15 18883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18883 : oddCount 18883 15 = 9 ∧ acceleratedOrbit 15 18883 = 11345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18883) = 3 ^ 9 * m + 11345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18883.1, data_15_18883.2]

/-- Complete interval computation for depth 15, residue 18884. -/
theorem bounds_15_18884 : exactInterval 15 18884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18884 : oddCount 18884 15 = 4 ∧ acceleratedOrbit 15 18884 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18884) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18884.1, data_15_18884.2]

/-- Complete interval computation for depth 15, residue 18885. -/
theorem bounds_15_18885 : exactInterval 15 18885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18885 : oddCount 18885 15 = 4 ∧ acceleratedOrbit 15 18885 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18885) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18885.1, data_15_18885.2]

/-- Complete interval computation for depth 15, residue 18886. -/
theorem bounds_15_18886 : exactInterval 15 18886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18886 : oddCount 18886 15 = 4 ∧ acceleratedOrbit 15 18886 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18886) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18886.1, data_15_18886.2]

/-- Complete interval computation for depth 15, residue 18887. -/
theorem bounds_15_18887 : exactInterval 15 18887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18887 : oddCount 18887 15 = 10 ∧ acceleratedOrbit 15 18887 = 34040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18887) = 3 ^ 10 * m + 34040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18887.1, data_15_18887.2]

/-- Complete interval computation for depth 15, residue 18888. -/
theorem bounds_15_18888 : exactInterval 15 18888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18888 : oddCount 18888 15 = 7 ∧ acceleratedOrbit 15 18888 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18888) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18888.1, data_15_18888.2]

/-- Complete interval computation for depth 15, residue 18889. -/
theorem bounds_15_18889 : exactInterval 15 18889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18889 : oddCount 18889 15 = 7 ∧ acceleratedOrbit 15 18889 = 1261 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18889) = 3 ^ 7 * m + 1261 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18889.1, data_15_18889.2]

/-- Complete interval computation for depth 15, residue 18890. -/
theorem bounds_15_18890 : exactInterval 15 18890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18890 : oddCount 18890 15 = 7 ∧ acceleratedOrbit 15 18890 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18890) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18890.1, data_15_18890.2]

/-- Complete interval computation for depth 15, residue 18891. -/
theorem bounds_15_18891 : exactInterval 15 18891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18891 : oddCount 18891 15 = 7 ∧ acceleratedOrbit 15 18891 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18891) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18891.1, data_15_18891.2]

/-- Complete interval computation for depth 15, residue 18892. -/
theorem bounds_15_18892 : exactInterval 15 18892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18892 : oddCount 18892 15 = 7 ∧ acceleratedOrbit 15 18892 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18892) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18892.1, data_15_18892.2]

/-- Complete interval computation for depth 15, residue 18893. -/
theorem bounds_15_18893 : exactInterval 15 18893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18893 : oddCount 18893 15 = 7 ∧ acceleratedOrbit 15 18893 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18893) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18893.1, data_15_18893.2]

/-- Complete interval computation for depth 15, residue 18894. -/
theorem bounds_15_18894 : exactInterval 15 18894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18894 : oddCount 18894 15 = 9 ∧ acceleratedOrbit 15 18894 = 11351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18894) = 3 ^ 9 * m + 11351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18894.1, data_15_18894.2]

/-- Complete interval computation for depth 15, residue 18895. -/
theorem bounds_15_18895 : exactInterval 15 18895 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18895) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18895 : oddCount 18895 15 = 9 ∧ acceleratedOrbit 15 18895 = 11351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18895) = 3 ^ 9 * m + 11351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18895.1, data_15_18895.2]

/-- Complete interval computation for depth 15, residue 18896. -/
theorem bounds_15_18896 : exactInterval 15 18896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18896 : oddCount 18896 15 = 6 ∧ acceleratedOrbit 15 18896 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18896) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18896.1, data_15_18896.2]

/-- Complete interval computation for depth 15, residue 18897. -/
theorem bounds_15_18897 : exactInterval 15 18897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18897 : oddCount 18897 15 = 7 ∧ acceleratedOrbit 15 18897 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18897) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18897.1, data_15_18897.2]

/-- Complete interval computation for depth 15, residue 18898. -/
theorem bounds_15_18898 : exactInterval 15 18898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18898 : oddCount 18898 15 = 7 ∧ acceleratedOrbit 15 18898 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18898) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18898.1, data_15_18898.2]

/-- Complete interval computation for depth 15, residue 18899. -/
theorem bounds_15_18899 : exactInterval 15 18899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18899 : oddCount 18899 15 = 7 ∧ acceleratedOrbit 15 18899 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18899) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18899.1, data_15_18899.2]

/-- Complete interval computation for depth 15, residue 18900. -/
theorem bounds_15_18900 : exactInterval 15 18900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18900 : oddCount 18900 15 = 6 ∧ acceleratedOrbit 15 18900 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18900) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18900.1, data_15_18900.2]

/-- Complete interval computation for depth 15, residue 18901. -/
theorem bounds_15_18901 : exactInterval 15 18901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18901 : oddCount 18901 15 = 6 ∧ acceleratedOrbit 15 18901 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18901) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18901.1, data_15_18901.2]

/-- Complete interval computation for depth 15, residue 18902. -/
theorem bounds_15_18902 : exactInterval 15 18902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18902 : oddCount 18902 15 = 9 ∧ acceleratedOrbit 15 18902 = 11357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18902) = 3 ^ 9 * m + 11357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18902.1, data_15_18902.2]

/-- Complete interval computation for depth 15, residue 18903. -/
theorem bounds_15_18903 : exactInterval 15 18903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18903 : oddCount 18903 15 = 9 ∧ acceleratedOrbit 15 18903 = 11357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18903) = 3 ^ 9 * m + 11357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18903.1, data_15_18903.2]

/-- Complete interval computation for depth 15, residue 18904. -/
theorem bounds_15_18904 : exactInterval 15 18904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18904 : oddCount 18904 15 = 6 ∧ acceleratedOrbit 15 18904 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18904) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18904.1, data_15_18904.2]

/-- Complete interval computation for depth 15, residue 18905. -/
theorem bounds_15_18905 : exactInterval 15 18905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18905 : oddCount 18905 15 = 6 ∧ acceleratedOrbit 15 18905 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18905) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18905.1, data_15_18905.2]

/-- Complete interval computation for depth 15, residue 18906. -/
theorem bounds_15_18906 : exactInterval 15 18906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18906 : oddCount 18906 15 = 6 ∧ acceleratedOrbit 15 18906 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18906) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18906.1, data_15_18906.2]

end Collatz.Research.PassageAtlas.Batch0577
