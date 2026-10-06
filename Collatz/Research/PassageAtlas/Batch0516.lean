import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0516

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16875. -/
theorem bounds_15_16875 : exactInterval 15 16875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16875 : oddCount 16875 15 = 10 ∧ acceleratedOrbit 15 16875 = 30413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16875) = 3 ^ 10 * m + 30413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16875.1, data_15_16875.2]

/-- Complete interval computation for depth 15, residue 16876. -/
theorem bounds_15_16876 : exactInterval 15 16876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16876 : oddCount 16876 15 = 7 ∧ acceleratedOrbit 15 16876 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16876) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16876.1, data_15_16876.2]

/-- Complete interval computation for depth 15, residue 16877. -/
theorem bounds_15_16877 : exactInterval 15 16877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16877 : oddCount 16877 15 = 7 ∧ acceleratedOrbit 15 16877 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16877) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16877.1, data_15_16877.2]

/-- Complete interval computation for depth 15, residue 16878. -/
theorem bounds_15_16878 : exactInterval 15 16878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16878 : oddCount 16878 15 = 7 ∧ acceleratedOrbit 15 16878 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16878) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16878.1, data_15_16878.2]

/-- Complete interval computation for depth 15, residue 16879. -/
theorem bounds_15_16879 : exactInterval 15 16879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16879 : oddCount 16879 15 = 12 ∧ acceleratedOrbit 15 16879 = 273770 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16879) = 3 ^ 12 * m + 273770 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16879.1, data_15_16879.2]

/-- Complete interval computation for depth 15, residue 16880. -/
theorem bounds_15_16880 : exactInterval 15 16880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16880 : oddCount 16880 15 = 9 ∧ acceleratedOrbit 15 16880 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16880) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16880.1, data_15_16880.2]

/-- Complete interval computation for depth 15, residue 16881. -/
theorem bounds_15_16881 : exactInterval 15 16881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16881 : oddCount 16881 15 = 6 ∧ acceleratedOrbit 15 16881 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16881) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16881.1, data_15_16881.2]

/-- Complete interval computation for depth 15, residue 16882. -/
theorem bounds_15_16882 : exactInterval 15 16882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16882 : oddCount 16882 15 = 9 ∧ acceleratedOrbit 15 16882 = 10145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16882) = 3 ^ 9 * m + 10145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16882.1, data_15_16882.2]

/-- Complete interval computation for depth 15, residue 16883. -/
theorem bounds_15_16883 : exactInterval 15 16883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16883 : oddCount 16883 15 = 9 ∧ acceleratedOrbit 15 16883 = 10145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16883) = 3 ^ 9 * m + 10145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16883.1, data_15_16883.2]

/-- Complete interval computation for depth 15, residue 16884. -/
theorem bounds_15_16884 : exactInterval 15 16884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16884 : oddCount 16884 15 = 9 ∧ acceleratedOrbit 15 16884 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16884) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16884.1, data_15_16884.2]

/-- Complete interval computation for depth 15, residue 16885. -/
theorem bounds_15_16885 : exactInterval 15 16885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16885 : oddCount 16885 15 = 9 ∧ acceleratedOrbit 15 16885 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16885) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16885.1, data_15_16885.2]

/-- Complete interval computation for depth 15, residue 16886. -/
theorem bounds_15_16886 : exactInterval 15 16886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16886 : oddCount 16886 15 = 11 ∧ acceleratedOrbit 15 16886 = 91307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16886) = 3 ^ 11 * m + 91307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16886.1, data_15_16886.2]

/-- Complete interval computation for depth 15, residue 16887. -/
theorem bounds_15_16887 : exactInterval 15 16887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16887 : oddCount 16887 15 = 11 ∧ acceleratedOrbit 15 16887 = 91307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16887) = 3 ^ 11 * m + 91307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16887.1, data_15_16887.2]

/-- Complete interval computation for depth 15, residue 16888. -/
theorem bounds_15_16888 : exactInterval 15 16888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16888 : oddCount 16888 15 = 9 ∧ acceleratedOrbit 15 16888 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16888) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16888.1, data_15_16888.2]

/-- Complete interval computation for depth 15, residue 16889. -/
theorem bounds_15_16889 : exactInterval 15 16889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16889 : oddCount 16889 15 = 9 ∧ acceleratedOrbit 15 16889 = 10147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16889) = 3 ^ 9 * m + 10147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16889.1, data_15_16889.2]

/-- Complete interval computation for depth 15, residue 16890. -/
theorem bounds_15_16890 : exactInterval 15 16890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16890 : oddCount 16890 15 = 9 ∧ acceleratedOrbit 15 16890 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16890) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16890.1, data_15_16890.2]

/-- Complete interval computation for depth 15, residue 16891. -/
theorem bounds_15_16891 : exactInterval 15 16891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16891 : oddCount 16891 15 = 8 ∧ acceleratedOrbit 15 16891 = 3383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16891) = 3 ^ 8 * m + 3383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16891.1, data_15_16891.2]

/-- Complete interval computation for depth 15, residue 16892. -/
theorem bounds_15_16892 : exactInterval 15 16892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16892 : oddCount 16892 15 = 8 ∧ acceleratedOrbit 15 16892 = 3383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16892) = 3 ^ 8 * m + 3383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16892.1, data_15_16892.2]

/-- Complete interval computation for depth 15, residue 16893. -/
theorem bounds_15_16893 : exactInterval 15 16893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16893 : oddCount 16893 15 = 8 ∧ acceleratedOrbit 15 16893 = 3383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16893) = 3 ^ 8 * m + 3383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16893.1, data_15_16893.2]

/-- Complete interval computation for depth 15, residue 16894. -/
theorem bounds_15_16894 : exactInterval 15 16894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16894 : oddCount 16894 15 = 8 ∧ acceleratedOrbit 15 16894 = 3383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16894) = 3 ^ 8 * m + 3383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16894.1, data_15_16894.2]

/-- Complete interval computation for depth 15, residue 16895. -/
theorem bounds_15_16895 : exactInterval 15 16895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16895 : oddCount 16895 15 = 12 ∧ acceleratedOrbit 15 16895 = 274025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16895) = 3 ^ 12 * m + 274025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16895.1, data_15_16895.2]

/-- Complete interval computation for depth 15, residue 16896. -/
theorem bounds_15_16896 : exactInterval 15 16896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16896 : oddCount 16896 15 = 4 ∧ acceleratedOrbit 15 16896 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16896) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16896.1, data_15_16896.2]

/-- Complete interval computation for depth 15, residue 16897. -/
theorem bounds_15_16897 : exactInterval 15 16897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16897 : oddCount 16897 15 = 6 ∧ acceleratedOrbit 15 16897 = 376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16897) = 3 ^ 6 * m + 376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16897.1, data_15_16897.2]

/-- Complete interval computation for depth 15, residue 16898. -/
theorem bounds_15_16898 : exactInterval 15 16898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16898 : oddCount 16898 15 = 7 ∧ acceleratedOrbit 15 16898 = 1129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16898) = 3 ^ 7 * m + 1129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16898.1, data_15_16898.2]

/-- Complete interval computation for depth 15, residue 16899. -/
theorem bounds_15_16899 : exactInterval 15 16899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16899 : oddCount 16899 15 = 7 ∧ acceleratedOrbit 15 16899 = 1129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16899) = 3 ^ 7 * m + 1129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16899.1, data_15_16899.2]

/-- Complete interval computation for depth 15, residue 16900. -/
theorem bounds_15_16900 : exactInterval 15 16900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16900 : oddCount 16900 15 = 7 ∧ acceleratedOrbit 15 16900 = 1129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16900) = 3 ^ 7 * m + 1129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16900.1, data_15_16900.2]

/-- Complete interval computation for depth 15, residue 16901. -/
theorem bounds_15_16901 : exactInterval 15 16901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16901 : oddCount 16901 15 = 7 ∧ acceleratedOrbit 15 16901 = 1129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16901) = 3 ^ 7 * m + 1129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16901.1, data_15_16901.2]

/-- Complete interval computation for depth 15, residue 16902. -/
theorem bounds_15_16902 : exactInterval 15 16902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16902 : oddCount 16902 15 = 7 ∧ acceleratedOrbit 15 16902 = 1129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16902) = 3 ^ 7 * m + 1129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16902.1, data_15_16902.2]

/-- Complete interval computation for depth 15, residue 16903. -/
theorem bounds_15_16903 : exactInterval 15 16903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16903 : oddCount 16903 15 = 8 ∧ acceleratedOrbit 15 16903 = 3385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16903) = 3 ^ 8 * m + 3385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16903.1, data_15_16903.2]

/-- Complete interval computation for depth 15, residue 16904. -/
theorem bounds_15_16904 : exactInterval 15 16904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16904 : oddCount 16904 15 = 7 ∧ acceleratedOrbit 15 16904 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16904) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16904.1, data_15_16904.2]

/-- Complete interval computation for depth 15, residue 16905. -/
theorem bounds_15_16905 : exactInterval 15 16905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16905 : oddCount 16905 15 = 7 ∧ acceleratedOrbit 15 16905 = 1129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16905) = 3 ^ 7 * m + 1129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16905.1, data_15_16905.2]

/-- Complete interval computation for depth 15, residue 16906. -/
theorem bounds_15_16906 : exactInterval 15 16906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16906 : oddCount 16906 15 = 7 ∧ acceleratedOrbit 15 16906 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16906) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16906.1, data_15_16906.2]

/-- Complete interval computation for depth 15, residue 16907. -/
theorem bounds_15_16907 : exactInterval 15 16907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16907 : oddCount 16907 15 = 7 ∧ acceleratedOrbit 15 16907 = 1129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16907) = 3 ^ 7 * m + 1129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16907.1, data_15_16907.2]

end Collatz.Research.PassageAtlas.Batch0516
