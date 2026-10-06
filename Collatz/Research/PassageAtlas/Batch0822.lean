import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0822

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26902. -/
theorem bounds_15_26902 : exactInterval 15 26902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26902 : oddCount 26902 15 = 7 ∧ acceleratedOrbit 15 26902 = 1796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26902) = 3 ^ 7 * m + 1796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26902.1, data_15_26902.2]

/-- Complete interval computation for depth 15, residue 26903. -/
theorem bounds_15_26903 : exactInterval 15 26903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26903 : oddCount 26903 15 = 7 ∧ acceleratedOrbit 15 26903 = 1796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26903) = 3 ^ 7 * m + 1796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26903.1, data_15_26903.2]

/-- Complete interval computation for depth 15, residue 26904. -/
theorem bounds_15_26904 : exactInterval 15 26904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26904 : oddCount 26904 15 = 5 ∧ acceleratedOrbit 15 26904 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26904) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26904.1, data_15_26904.2]

/-- Complete interval computation for depth 15, residue 26905. -/
theorem bounds_15_26905 : exactInterval 15 26905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26905 : oddCount 26905 15 = 7 ∧ acceleratedOrbit 15 26905 = 1796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26905) = 3 ^ 7 * m + 1796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26905.1, data_15_26905.2]

/-- Complete interval computation for depth 15, residue 26906. -/
theorem bounds_15_26906 : exactInterval 15 26906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26906 : oddCount 26906 15 = 5 ∧ acceleratedOrbit 15 26906 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26906) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26906.1, data_15_26906.2]

/-- Complete interval computation for depth 15, residue 26907. -/
theorem bounds_15_26907 : exactInterval 15 26907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26907 : oddCount 26907 15 = 10 ∧ acceleratedOrbit 15 26907 = 48491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26907) = 3 ^ 10 * m + 48491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26907.1, data_15_26907.2]

/-- Complete interval computation for depth 15, residue 26908. -/
theorem bounds_15_26908 : exactInterval 15 26908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26908 : oddCount 26908 15 = 8 ∧ acceleratedOrbit 15 26908 = 5390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26908) = 3 ^ 8 * m + 5390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26908.1, data_15_26908.2]

/-- Complete interval computation for depth 15, residue 26909. -/
theorem bounds_15_26909 : exactInterval 15 26909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26909 : oddCount 26909 15 = 8 ∧ acceleratedOrbit 15 26909 = 5390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26909) = 3 ^ 8 * m + 5390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26909.1, data_15_26909.2]

/-- Complete interval computation for depth 15, residue 26910. -/
theorem bounds_15_26910 : exactInterval 15 26910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26910 : oddCount 26910 15 = 8 ∧ acceleratedOrbit 15 26910 = 5390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26910) = 3 ^ 8 * m + 5390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26910.1, data_15_26910.2]

/-- Complete interval computation for depth 15, residue 26911. -/
theorem bounds_15_26911 : exactInterval 15 26911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26911 : oddCount 26911 15 = 9 ∧ acceleratedOrbit 15 26911 = 16166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26911) = 3 ^ 9 * m + 16166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26911.1, data_15_26911.2]

/-- Complete interval computation for depth 15, residue 26912. -/
theorem bounds_15_26912 : exactInterval 15 26912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26912 : oddCount 26912 15 = 5 ∧ acceleratedOrbit 15 26912 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26912) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26912.1, data_15_26912.2]

/-- Complete interval computation for depth 15, residue 26913. -/
theorem bounds_15_26913 : exactInterval 15 26913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26913 : oddCount 26913 15 = 6 ∧ acceleratedOrbit 15 26913 = 599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26913) = 3 ^ 6 * m + 599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26913.1, data_15_26913.2]

/-- Complete interval computation for depth 15, residue 26914. -/
theorem bounds_15_26914 : exactInterval 15 26914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26914 : oddCount 26914 15 = 6 ∧ acceleratedOrbit 15 26914 = 599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26914) = 3 ^ 6 * m + 599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26914.1, data_15_26914.2]

/-- Complete interval computation for depth 15, residue 26915. -/
theorem bounds_15_26915 : exactInterval 15 26915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26915 : oddCount 26915 15 = 6 ∧ acceleratedOrbit 15 26915 = 599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26915) = 3 ^ 6 * m + 599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26915.1, data_15_26915.2]

/-- Complete interval computation for depth 15, residue 26916. -/
theorem bounds_15_26916 : exactInterval 15 26916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26916 : oddCount 26916 15 = 6 ∧ acceleratedOrbit 15 26916 = 599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26916) = 3 ^ 6 * m + 599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26916.1, data_15_26916.2]

/-- Complete interval computation for depth 15, residue 26917. -/
theorem bounds_15_26917 : exactInterval 15 26917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26917 : oddCount 26917 15 = 6 ∧ acceleratedOrbit 15 26917 = 599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26917) = 3 ^ 6 * m + 599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26917.1, data_15_26917.2]

/-- Complete interval computation for depth 15, residue 26918. -/
theorem bounds_15_26918 : exactInterval 15 26918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26918 : oddCount 26918 15 = 6 ∧ acceleratedOrbit 15 26918 = 599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26918) = 3 ^ 6 * m + 599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26918.1, data_15_26918.2]

/-- Complete interval computation for depth 15, residue 26919. -/
theorem bounds_15_26919 : exactInterval 15 26919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26919 : oddCount 26919 15 = 9 ∧ acceleratedOrbit 15 26919 = 16172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26919) = 3 ^ 9 * m + 16172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26919.1, data_15_26919.2]

/-- Complete interval computation for depth 15, residue 26920. -/
theorem bounds_15_26920 : exactInterval 15 26920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26920 : oddCount 26920 15 = 5 ∧ acceleratedOrbit 15 26920 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26920) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26920.1, data_15_26920.2]

/-- Complete interval computation for depth 15, residue 26921. -/
theorem bounds_15_26921 : exactInterval 15 26921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26921 : oddCount 26921 15 = 10 ∧ acceleratedOrbit 15 26921 = 48518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26921) = 3 ^ 10 * m + 48518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26921.1, data_15_26921.2]

/-- Complete interval computation for depth 15, residue 26922. -/
theorem bounds_15_26922 : exactInterval 15 26922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26922 : oddCount 26922 15 = 5 ∧ acceleratedOrbit 15 26922 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26922) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26922.1, data_15_26922.2]

/-- Complete interval computation for depth 15, residue 26923. -/
theorem bounds_15_26923 : exactInterval 15 26923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26923 : oddCount 26923 15 = 9 ∧ acceleratedOrbit 15 26923 = 16175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26923) = 3 ^ 9 * m + 16175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26923.1, data_15_26923.2]

/-- Complete interval computation for depth 15, residue 26924. -/
theorem bounds_15_26924 : exactInterval 15 26924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26924 : oddCount 26924 15 = 5 ∧ acceleratedOrbit 15 26924 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26924) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26924.1, data_15_26924.2]

/-- Complete interval computation for depth 15, residue 26925. -/
theorem bounds_15_26925 : exactInterval 15 26925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26925 : oddCount 26925 15 = 5 ∧ acceleratedOrbit 15 26925 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26925) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26925.1, data_15_26925.2]

/-- Complete interval computation for depth 15, residue 26926. -/
theorem bounds_15_26926 : exactInterval 15 26926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26926 : oddCount 26926 15 = 5 ∧ acceleratedOrbit 15 26926 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26926) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26926.1, data_15_26926.2]

/-- Complete interval computation for depth 15, residue 26927. -/
theorem bounds_15_26927 : exactInterval 15 26927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26927 : oddCount 26927 15 = 8 ∧ acceleratedOrbit 15 26927 = 5392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26927) = 3 ^ 8 * m + 5392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26927.1, data_15_26927.2]

/-- Complete interval computation for depth 15, residue 26928. -/
theorem bounds_15_26928 : exactInterval 15 26928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26928 : oddCount 26928 15 = 5 ∧ acceleratedOrbit 15 26928 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26928) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26928.1, data_15_26928.2]

/-- Complete interval computation for depth 15, residue 26929. -/
theorem bounds_15_26929 : exactInterval 15 26929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26929 : oddCount 26929 15 = 7 ∧ acceleratedOrbit 15 26929 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26929) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26929.1, data_15_26929.2]

/-- Complete interval computation for depth 15, residue 26930. -/
theorem bounds_15_26930 : exactInterval 15 26930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26930 : oddCount 26930 15 = 7 ∧ acceleratedOrbit 15 26930 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26930) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26930.1, data_15_26930.2]

/-- Complete interval computation for depth 15, residue 26931. -/
theorem bounds_15_26931 : exactInterval 15 26931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26931 : oddCount 26931 15 = 7 ∧ acceleratedOrbit 15 26931 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26931) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26931.1, data_15_26931.2]

/-- Complete interval computation for depth 15, residue 26932. -/
theorem bounds_15_26932 : exactInterval 15 26932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26932 : oddCount 26932 15 = 5 ∧ acceleratedOrbit 15 26932 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26932) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26932.1, data_15_26932.2]

/-- Complete interval computation for depth 15, residue 26933. -/
theorem bounds_15_26933 : exactInterval 15 26933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26933 : oddCount 26933 15 = 5 ∧ acceleratedOrbit 15 26933 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26933) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26933.1, data_15_26933.2]

/-- Complete interval computation for depth 15, residue 26934. -/
theorem bounds_15_26934 : exactInterval 15 26934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26934 : oddCount 26934 15 = 9 ∧ acceleratedOrbit 15 26934 = 16181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26934) = 3 ^ 9 * m + 16181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26934.1, data_15_26934.2]

end Collatz.Research.PassageAtlas.Batch0822
