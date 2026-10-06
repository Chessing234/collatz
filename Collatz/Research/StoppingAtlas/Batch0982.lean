import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0982

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7900. -/
theorem bounds_13_7900 : exactInterval 13 7900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7900 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7900) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7900 : oddCount 7900 13 = 6 ∧ acceleratedOrbit 13 7900 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7900 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7900) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7900.1, data_13_7900.2]

/-- Complete interval computation for depth 13, residue 7901. -/
theorem bounds_13_7901 : exactInterval 13 7901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7901 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7901) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7901 : oddCount 7901 13 = 6 ∧ acceleratedOrbit 13 7901 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7901 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7901) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7901.1, data_13_7901.2]

/-- Complete interval computation for depth 13, residue 7902. -/
theorem bounds_13_7902 : exactInterval 13 7902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7902 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7902) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7902 : oddCount 7902 13 = 8 ∧ acceleratedOrbit 13 7902 = 6331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7902 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7902) = 3 ^ 8 * m + 6331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7902.1, data_13_7902.2]

/-- Complete interval computation for depth 13, residue 7903. -/
theorem bounds_13_7903 : exactInterval 13 7903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7903 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7903) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7903 : oddCount 7903 13 = 8 ∧ acceleratedOrbit 13 7903 = 6331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7903 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7903) = 3 ^ 8 * m + 6331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7903.1, data_13_7903.2]

/-- Complete interval computation for depth 13, residue 7904. -/
theorem bounds_13_7904 : exactInterval 13 7904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7904 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7904) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7904 : oddCount 7904 13 = 5 ∧ acceleratedOrbit 13 7904 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7904 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7904) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7904.1, data_13_7904.2]

/-- Complete interval computation for depth 13, residue 7905. -/
theorem bounds_13_7905 : exactInterval 13 7905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7905 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7905) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7905 : oddCount 7905 13 = 7 ∧ acceleratedOrbit 13 7905 = 2111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7905 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7905) = 3 ^ 7 * m + 2111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7905.1, data_13_7905.2]

/-- Complete interval computation for depth 13, residue 7906. -/
theorem bounds_13_7906 : exactInterval 13 7906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7906 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7906) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7906 : oddCount 7906 13 = 5 ∧ acceleratedOrbit 13 7906 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7906 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7906) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7906.1, data_13_7906.2]

/-- Complete interval computation for depth 13, residue 7907. -/
theorem bounds_13_7907 : exactInterval 13 7907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7907 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7907) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7907 : oddCount 7907 13 = 5 ∧ acceleratedOrbit 13 7907 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7907 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7907) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7907.1, data_13_7907.2]

/-- Complete interval computation for depth 13, residue 7908. -/
theorem bounds_13_7908 : exactInterval 13 7908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7908 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7908) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7908 : oddCount 7908 13 = 5 ∧ acceleratedOrbit 13 7908 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7908 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7908) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7908.1, data_13_7908.2]

/-- Complete interval computation for depth 13, residue 7909. -/
theorem bounds_13_7909 : exactInterval 13 7909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7909 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7909) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7909 : oddCount 7909 13 = 5 ∧ acceleratedOrbit 13 7909 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7909 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7909) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7909.1, data_13_7909.2]

/-- Complete interval computation for depth 13, residue 7910. -/
theorem bounds_13_7910 : exactInterval 13 7910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7910 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7910) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7910 : oddCount 7910 13 = 5 ∧ acceleratedOrbit 13 7910 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7910 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7910) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7910.1, data_13_7910.2]

/-- Complete interval computation for depth 13, residue 7911. -/
theorem bounds_13_7911 : exactInterval 13 7911 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7911 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7911) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7911 : oddCount 7911 13 = 8 ∧ acceleratedOrbit 13 7911 = 6337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7911 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7911) = 3 ^ 8 * m + 6337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7911.1, data_13_7911.2]

/-- Complete interval computation for depth 13, residue 7912. -/
theorem bounds_13_7912 : exactInterval 13 7912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7912 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7912) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7912 : oddCount 7912 13 = 5 ∧ acceleratedOrbit 13 7912 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7912 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7912) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7912.1, data_13_7912.2]

/-- Complete interval computation for depth 13, residue 7913. -/
theorem bounds_13_7913 : exactInterval 13 7913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7913 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7913) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7913 : oddCount 7913 13 = 7 ∧ acceleratedOrbit 13 7913 = 2113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7913 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7913) = 3 ^ 7 * m + 2113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7913.1, data_13_7913.2]

/-- Complete interval computation for depth 13, residue 7914. -/
theorem bounds_13_7914 : exactInterval 13 7914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7914 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7914) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7914 : oddCount 7914 13 = 5 ∧ acceleratedOrbit 13 7914 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7914 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7914) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7914.1, data_13_7914.2]

end Collatz.Research.StoppingAtlas.Batch0982
