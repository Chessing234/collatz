import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0425

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13893. -/
theorem bounds_15_13893 : exactInterval 15 13893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13893 : oddCount 13893 15 = 6 ∧ acceleratedOrbit 15 13893 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13893) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13893.1, data_15_13893.2]

/-- Complete interval computation for depth 15, residue 13894. -/
theorem bounds_15_13894 : exactInterval 15 13894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13894 : oddCount 13894 15 = 6 ∧ acceleratedOrbit 15 13894 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13894) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13894.1, data_15_13894.2]

/-- Complete interval computation for depth 15, residue 13895. -/
theorem bounds_15_13895 : exactInterval 15 13895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13895 : oddCount 13895 15 = 8 ∧ acceleratedOrbit 15 13895 = 2783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13895) = 3 ^ 8 * m + 2783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13895.1, data_15_13895.2]

/-- Complete interval computation for depth 15, residue 13896. -/
theorem bounds_15_13896 : exactInterval 15 13896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13896 : oddCount 13896 15 = 6 ∧ acceleratedOrbit 15 13896 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13896) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13896.1, data_15_13896.2]

/-- Complete interval computation for depth 15, residue 13897. -/
theorem bounds_15_13897 : exactInterval 15 13897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13897 : oddCount 13897 15 = 10 ∧ acceleratedOrbit 15 13897 = 25049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13897) = 3 ^ 10 * m + 25049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13897.1, data_15_13897.2]

/-- Complete interval computation for depth 15, residue 13898. -/
theorem bounds_15_13898 : exactInterval 15 13898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13898 : oddCount 13898 15 = 6 ∧ acceleratedOrbit 15 13898 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13898) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13898.1, data_15_13898.2]

/-- Complete interval computation for depth 15, residue 13899. -/
theorem bounds_15_13899 : exactInterval 15 13899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13899 : oddCount 13899 15 = 6 ∧ acceleratedOrbit 15 13899 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13899) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13899.1, data_15_13899.2]

/-- Complete interval computation for depth 15, residue 13900. -/
theorem bounds_15_13900 : exactInterval 15 13900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13900 : oddCount 13900 15 = 6 ∧ acceleratedOrbit 15 13900 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13900) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13900.1, data_15_13900.2]

/-- Complete interval computation for depth 15, residue 13901. -/
theorem bounds_15_13901 : exactInterval 15 13901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13901 : oddCount 13901 15 = 6 ∧ acceleratedOrbit 15 13901 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13901) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13901.1, data_15_13901.2]

/-- Complete interval computation for depth 15, residue 13902. -/
theorem bounds_15_13902 : exactInterval 15 13902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13902 : oddCount 13902 15 = 9 ∧ acceleratedOrbit 15 13902 = 8353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13902) = 3 ^ 9 * m + 8353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13902.1, data_15_13902.2]

/-- Complete interval computation for depth 15, residue 13903. -/
theorem bounds_15_13903 : exactInterval 15 13903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13903 : oddCount 13903 15 = 9 ∧ acceleratedOrbit 15 13903 = 8353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13903) = 3 ^ 9 * m + 8353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13903.1, data_15_13903.2]

/-- Complete interval computation for depth 15, residue 13904. -/
theorem bounds_15_13904 : exactInterval 15 13904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13904 : oddCount 13904 15 = 4 ∧ acceleratedOrbit 15 13904 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13904) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13904.1, data_15_13904.2]

/-- Complete interval computation for depth 15, residue 13905. -/
theorem bounds_15_13905 : exactInterval 15 13905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13905 : oddCount 13905 15 = 9 ∧ acceleratedOrbit 15 13905 = 8356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13905) = 3 ^ 9 * m + 8356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13905.1, data_15_13905.2]

/-- Complete interval computation for depth 15, residue 13906. -/
theorem bounds_15_13906 : exactInterval 15 13906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13906 : oddCount 13906 15 = 9 ∧ acceleratedOrbit 15 13906 = 8356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13906) = 3 ^ 9 * m + 8356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13906.1, data_15_13906.2]

/-- Complete interval computation for depth 15, residue 13907. -/
theorem bounds_15_13907 : exactInterval 15 13907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13907 : oddCount 13907 15 = 9 ∧ acceleratedOrbit 15 13907 = 8356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13907) = 3 ^ 9 * m + 8356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13907.1, data_15_13907.2]

/-- Complete interval computation for depth 15, residue 13908. -/
theorem bounds_15_13908 : exactInterval 15 13908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13908 : oddCount 13908 15 = 4 ∧ acceleratedOrbit 15 13908 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13908) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13908.1, data_15_13908.2]

/-- Complete interval computation for depth 15, residue 13909. -/
theorem bounds_15_13909 : exactInterval 15 13909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13909 : oddCount 13909 15 = 4 ∧ acceleratedOrbit 15 13909 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13909) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13909.1, data_15_13909.2]

/-- Complete interval computation for depth 15, residue 13910. -/
theorem bounds_15_13910 : exactInterval 15 13910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13910 : oddCount 13910 15 = 7 ∧ acceleratedOrbit 15 13910 = 929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13910) = 3 ^ 7 * m + 929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13910.1, data_15_13910.2]

/-- Complete interval computation for depth 15, residue 13911. -/
theorem bounds_15_13911 : exactInterval 15 13911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13911 : oddCount 13911 15 = 7 ∧ acceleratedOrbit 15 13911 = 929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13911) = 3 ^ 7 * m + 929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13911.1, data_15_13911.2]

/-- Complete interval computation for depth 15, residue 13912. -/
theorem bounds_15_13912 : exactInterval 15 13912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13912 : oddCount 13912 15 = 7 ∧ acceleratedOrbit 15 13912 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13912) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13912.1, data_15_13912.2]

/-- Complete interval computation for depth 15, residue 13913. -/
theorem bounds_15_13913 : exactInterval 15 13913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13913 : oddCount 13913 15 = 7 ∧ acceleratedOrbit 15 13913 = 929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13913) = 3 ^ 7 * m + 929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13913.1, data_15_13913.2]

/-- Complete interval computation for depth 15, residue 13914. -/
theorem bounds_15_13914 : exactInterval 15 13914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13914 : oddCount 13914 15 = 7 ∧ acceleratedOrbit 15 13914 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13914) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13914.1, data_15_13914.2]

/-- Complete interval computation for depth 15, residue 13915. -/
theorem bounds_15_13915 : exactInterval 15 13915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13915 : oddCount 13915 15 = 9 ∧ acceleratedOrbit 15 13915 = 8360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13915) = 3 ^ 9 * m + 8360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13915.1, data_15_13915.2]

/-- Complete interval computation for depth 15, residue 13916. -/
theorem bounds_15_13916 : exactInterval 15 13916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13916 : oddCount 13916 15 = 7 ∧ acceleratedOrbit 15 13916 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13916) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13916.1, data_15_13916.2]

/-- Complete interval computation for depth 15, residue 13917. -/
theorem bounds_15_13917 : exactInterval 15 13917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13917 : oddCount 13917 15 = 7 ∧ acceleratedOrbit 15 13917 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13917) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13917.1, data_15_13917.2]

/-- Complete interval computation for depth 15, residue 13918. -/
theorem bounds_15_13918 : exactInterval 15 13918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13918 : oddCount 13918 15 = 9 ∧ acceleratedOrbit 15 13918 = 8363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13918) = 3 ^ 9 * m + 8363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13918.1, data_15_13918.2]

/-- Complete interval computation for depth 15, residue 13919. -/
theorem bounds_15_13919 : exactInterval 15 13919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13919 : oddCount 13919 15 = 9 ∧ acceleratedOrbit 15 13919 = 8363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13919) = 3 ^ 9 * m + 8363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13919.1, data_15_13919.2]

/-- Complete interval computation for depth 15, residue 13920. -/
theorem bounds_15_13920 : exactInterval 15 13920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13920 : oddCount 13920 15 = 4 ∧ acceleratedOrbit 15 13920 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13920) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13920.1, data_15_13920.2]

/-- Complete interval computation for depth 15, residue 13921. -/
theorem bounds_15_13921 : exactInterval 15 13921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13921 : oddCount 13921 15 = 6 ∧ acceleratedOrbit 15 13921 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13921) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13921.1, data_15_13921.2]

/-- Complete interval computation for depth 15, residue 13922. -/
theorem bounds_15_13922 : exactInterval 15 13922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13922 : oddCount 13922 15 = 7 ∧ acceleratedOrbit 15 13922 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13922) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13922.1, data_15_13922.2]

/-- Complete interval computation for depth 15, residue 13923. -/
theorem bounds_15_13923 : exactInterval 15 13923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13923 : oddCount 13923 15 = 7 ∧ acceleratedOrbit 15 13923 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13923) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13923.1, data_15_13923.2]

/-- Complete interval computation for depth 15, residue 13924. -/
theorem bounds_15_13924 : exactInterval 15 13924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13924 : oddCount 13924 15 = 7 ∧ acceleratedOrbit 15 13924 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13924) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13924.1, data_15_13924.2]

/-- Complete interval computation for depth 15, residue 13925. -/
theorem bounds_15_13925 : exactInterval 15 13925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13925 : oddCount 13925 15 = 7 ∧ acceleratedOrbit 15 13925 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13925) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13925.1, data_15_13925.2]

end Collatz.Research.PassageAtlas.Batch0425
