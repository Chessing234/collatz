import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0608

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19890. -/
theorem bounds_15_19890 : exactInterval 15 19890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19890 : oddCount 19890 15 = 6 ∧ acceleratedOrbit 15 19890 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19890) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19890.1, data_15_19890.2]

/-- Complete interval computation for depth 15, residue 19891. -/
theorem bounds_15_19891 : exactInterval 15 19891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19891 : oddCount 19891 15 = 6 ∧ acceleratedOrbit 15 19891 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19891) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19891.1, data_15_19891.2]

/-- Complete interval computation for depth 15, residue 19892. -/
theorem bounds_15_19892 : exactInterval 15 19892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19892 : oddCount 19892 15 = 6 ∧ acceleratedOrbit 15 19892 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19892) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19892.1, data_15_19892.2]

/-- Complete interval computation for depth 15, residue 19893. -/
theorem bounds_15_19893 : exactInterval 15 19893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19893 : oddCount 19893 15 = 6 ∧ acceleratedOrbit 15 19893 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19893) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19893.1, data_15_19893.2]

/-- Complete interval computation for depth 15, residue 19894. -/
theorem bounds_15_19894 : exactInterval 15 19894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19894 : oddCount 19894 15 = 7 ∧ acceleratedOrbit 15 19894 = 1328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19894) = 3 ^ 7 * m + 1328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19894.1, data_15_19894.2]

/-- Complete interval computation for depth 15, residue 19895. -/
theorem bounds_15_19895 : exactInterval 15 19895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19895 : oddCount 19895 15 = 7 ∧ acceleratedOrbit 15 19895 = 1328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19895) = 3 ^ 7 * m + 1328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19895.1, data_15_19895.2]

/-- Complete interval computation for depth 15, residue 19896. -/
theorem bounds_15_19896 : exactInterval 15 19896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19896 : oddCount 19896 15 = 6 ∧ acceleratedOrbit 15 19896 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19896) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19896.1, data_15_19896.2]

/-- Complete interval computation for depth 15, residue 19897. -/
theorem bounds_15_19897 : exactInterval 15 19897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19897 : oddCount 19897 15 = 6 ∧ acceleratedOrbit 15 19897 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19897) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19897.1, data_15_19897.2]

/-- Complete interval computation for depth 15, residue 19898. -/
theorem bounds_15_19898 : exactInterval 15 19898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19898 : oddCount 19898 15 = 6 ∧ acceleratedOrbit 15 19898 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19898) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19898.1, data_15_19898.2]

/-- Complete interval computation for depth 15, residue 19899. -/
theorem bounds_15_19899 : exactInterval 15 19899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19899 : oddCount 19899 15 = 8 ∧ acceleratedOrbit 15 19899 = 3986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19899) = 3 ^ 8 * m + 3986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19899.1, data_15_19899.2]

/-- Complete interval computation for depth 15, residue 19900. -/
theorem bounds_15_19900 : exactInterval 15 19900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19900 : oddCount 19900 15 = 8 ∧ acceleratedOrbit 15 19900 = 3986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19900) = 3 ^ 8 * m + 3986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19900.1, data_15_19900.2]

/-- Complete interval computation for depth 15, residue 19901. -/
theorem bounds_15_19901 : exactInterval 15 19901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19901 : oddCount 19901 15 = 8 ∧ acceleratedOrbit 15 19901 = 3986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19901) = 3 ^ 8 * m + 3986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19901.1, data_15_19901.2]

/-- Complete interval computation for depth 15, residue 19902. -/
theorem bounds_15_19902 : exactInterval 15 19902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19902 : oddCount 19902 15 = 8 ∧ acceleratedOrbit 15 19902 = 3986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19902) = 3 ^ 8 * m + 3986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19902.1, data_15_19902.2]

/-- Complete interval computation for depth 15, residue 19903. -/
theorem bounds_15_19903 : exactInterval 15 19903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19903 : oddCount 19903 15 = 12 ∧ acceleratedOrbit 15 19903 = 322811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19903) = 3 ^ 12 * m + 322811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19903.1, data_15_19903.2]

/-- Complete interval computation for depth 15, residue 19904. -/
theorem bounds_15_19904 : exactInterval 15 19904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19904 : oddCount 19904 15 = 6 ∧ acceleratedOrbit 15 19904 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19904) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19904.1, data_15_19904.2]

/-- Complete interval computation for depth 15, residue 19905. -/
theorem bounds_15_19905 : exactInterval 15 19905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19905 : oddCount 19905 15 = 10 ∧ acceleratedOrbit 15 19905 = 35882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19905) = 3 ^ 10 * m + 35882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19905.1, data_15_19905.2]

/-- Complete interval computation for depth 15, residue 19906. -/
theorem bounds_15_19906 : exactInterval 15 19906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19906 : oddCount 19906 15 = 10 ∧ acceleratedOrbit 15 19906 = 35882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19906) = 3 ^ 10 * m + 35882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19906.1, data_15_19906.2]

/-- Complete interval computation for depth 15, residue 19907. -/
theorem bounds_15_19907 : exactInterval 15 19907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19907 : oddCount 19907 15 = 10 ∧ acceleratedOrbit 15 19907 = 35882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19907) = 3 ^ 10 * m + 35882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19907.1, data_15_19907.2]

/-- Complete interval computation for depth 15, residue 19908. -/
theorem bounds_15_19908 : exactInterval 15 19908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19908 : oddCount 19908 15 = 6 ∧ acceleratedOrbit 15 19908 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19908) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19908.1, data_15_19908.2]

/-- Complete interval computation for depth 15, residue 19909. -/
theorem bounds_15_19909 : exactInterval 15 19909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19909 : oddCount 19909 15 = 6 ∧ acceleratedOrbit 15 19909 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19909) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19909.1, data_15_19909.2]

/-- Complete interval computation for depth 15, residue 19910. -/
theorem bounds_15_19910 : exactInterval 15 19910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19910 : oddCount 19910 15 = 6 ∧ acceleratedOrbit 15 19910 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19910) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19910.1, data_15_19910.2]

/-- Complete interval computation for depth 15, residue 19911. -/
theorem bounds_15_19911 : exactInterval 15 19911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19911 : oddCount 19911 15 = 6 ∧ acceleratedOrbit 15 19911 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19911) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19911.1, data_15_19911.2]

/-- Complete interval computation for depth 15, residue 19912. -/
theorem bounds_15_19912 : exactInterval 15 19912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19912 : oddCount 19912 15 = 5 ∧ acceleratedOrbit 15 19912 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19912) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19912.1, data_15_19912.2]

/-- Complete interval computation for depth 15, residue 19913. -/
theorem bounds_15_19913 : exactInterval 15 19913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19913 : oddCount 19913 15 = 8 ∧ acceleratedOrbit 15 19913 = 3989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19913) = 3 ^ 8 * m + 3989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19913.1, data_15_19913.2]

/-- Complete interval computation for depth 15, residue 19914. -/
theorem bounds_15_19914 : exactInterval 15 19914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19914 : oddCount 19914 15 = 5 ∧ acceleratedOrbit 15 19914 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19914) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19914.1, data_15_19914.2]

/-- Complete interval computation for depth 15, residue 19915. -/
theorem bounds_15_19915 : exactInterval 15 19915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19915 : oddCount 19915 15 = 8 ∧ acceleratedOrbit 15 19915 = 3989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19915) = 3 ^ 8 * m + 3989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19915.1, data_15_19915.2]

/-- Complete interval computation for depth 15, residue 19916. -/
theorem bounds_15_19916 : exactInterval 15 19916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19916 : oddCount 19916 15 = 5 ∧ acceleratedOrbit 15 19916 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19916) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19916.1, data_15_19916.2]

/-- Complete interval computation for depth 15, residue 19917. -/
theorem bounds_15_19917 : exactInterval 15 19917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19917 : oddCount 19917 15 = 5 ∧ acceleratedOrbit 15 19917 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19917) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19917.1, data_15_19917.2]

/-- Complete interval computation for depth 15, residue 19918. -/
theorem bounds_15_19918 : exactInterval 15 19918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19918 : oddCount 19918 15 = 9 ∧ acceleratedOrbit 15 19918 = 11966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19918) = 3 ^ 9 * m + 11966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19918.1, data_15_19918.2]

/-- Complete interval computation for depth 15, residue 19919. -/
theorem bounds_15_19919 : exactInterval 15 19919 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19919) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19919 : oddCount 19919 15 = 9 ∧ acceleratedOrbit 15 19919 = 11966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19919) = 3 ^ 9 * m + 11966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19919.1, data_15_19919.2]

/-- Complete interval computation for depth 15, residue 19920. -/
theorem bounds_15_19920 : exactInterval 15 19920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19920 : oddCount 19920 15 = 6 ∧ acceleratedOrbit 15 19920 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19920) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19920.1, data_15_19920.2]

/-- Complete interval computation for depth 15, residue 19921. -/
theorem bounds_15_19921 : exactInterval 15 19921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19921 : oddCount 19921 15 = 5 ∧ acceleratedOrbit 15 19921 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19921) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19921.1, data_15_19921.2]

end Collatz.Research.PassageAtlas.Batch0608
