import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0517

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16908. -/
theorem bounds_15_16908 : exactInterval 15 16908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16908 : oddCount 16908 15 = 7 ∧ acceleratedOrbit 15 16908 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16908) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16908.1, data_15_16908.2]

/-- Complete interval computation for depth 15, residue 16909. -/
theorem bounds_15_16909 : exactInterval 15 16909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16909 : oddCount 16909 15 = 7 ∧ acceleratedOrbit 15 16909 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16909) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16909.1, data_15_16909.2]

/-- Complete interval computation for depth 15, residue 16910. -/
theorem bounds_15_16910 : exactInterval 15 16910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16910 : oddCount 16910 15 = 10 ∧ acceleratedOrbit 15 16910 = 30482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16910) = 3 ^ 10 * m + 30482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16910.1, data_15_16910.2]

/-- Complete interval computation for depth 15, residue 16911. -/
theorem bounds_15_16911 : exactInterval 15 16911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16911 : oddCount 16911 15 = 10 ∧ acceleratedOrbit 15 16911 = 30482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16911) = 3 ^ 10 * m + 30482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16911.1, data_15_16911.2]

/-- Complete interval computation for depth 15, residue 16912. -/
theorem bounds_15_16912 : exactInterval 15 16912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16912 : oddCount 16912 15 = 7 ∧ acceleratedOrbit 15 16912 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16912) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16912.1, data_15_16912.2]

/-- Complete interval computation for depth 15, residue 16913. -/
theorem bounds_15_16913 : exactInterval 15 16913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16913 : oddCount 16913 15 = 7 ∧ acceleratedOrbit 15 16913 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16913) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16913.1, data_15_16913.2]

/-- Complete interval computation for depth 15, residue 16914. -/
theorem bounds_15_16914 : exactInterval 15 16914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16914 : oddCount 16914 15 = 8 ∧ acceleratedOrbit 15 16914 = 3388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16914) = 3 ^ 8 * m + 3388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16914.1, data_15_16914.2]

/-- Complete interval computation for depth 15, residue 16915. -/
theorem bounds_15_16915 : exactInterval 15 16915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16915 : oddCount 16915 15 = 8 ∧ acceleratedOrbit 15 16915 = 3388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16915) = 3 ^ 8 * m + 3388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16915.1, data_15_16915.2]

/-- Complete interval computation for depth 15, residue 16916. -/
theorem bounds_15_16916 : exactInterval 15 16916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16916 : oddCount 16916 15 = 7 ∧ acceleratedOrbit 15 16916 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16916) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16916.1, data_15_16916.2]

/-- Complete interval computation for depth 15, residue 16917. -/
theorem bounds_15_16917 : exactInterval 15 16917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16917 : oddCount 16917 15 = 7 ∧ acceleratedOrbit 15 16917 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16917) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16917.1, data_15_16917.2]

/-- Complete interval computation for depth 15, residue 16918. -/
theorem bounds_15_16918 : exactInterval 15 16918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16918 : oddCount 16918 15 = 6 ∧ acceleratedOrbit 15 16918 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16918) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16918.1, data_15_16918.2]

/-- Complete interval computation for depth 15, residue 16919. -/
theorem bounds_15_16919 : exactInterval 15 16919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16919 : oddCount 16919 15 = 6 ∧ acceleratedOrbit 15 16919 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16919) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16919.1, data_15_16919.2]

/-- Complete interval computation for depth 15, residue 16920. -/
theorem bounds_15_16920 : exactInterval 15 16920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16920 : oddCount 16920 15 = 7 ∧ acceleratedOrbit 15 16920 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16920) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16920.1, data_15_16920.2]

/-- Complete interval computation for depth 15, residue 16921. -/
theorem bounds_15_16921 : exactInterval 15 16921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16921 : oddCount 16921 15 = 6 ∧ acceleratedOrbit 15 16921 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16921) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16921.1, data_15_16921.2]

/-- Complete interval computation for depth 15, residue 16922. -/
theorem bounds_15_16922 : exactInterval 15 16922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16922 : oddCount 16922 15 = 7 ∧ acceleratedOrbit 15 16922 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16922) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16922.1, data_15_16922.2]

/-- Complete interval computation for depth 15, residue 16923. -/
theorem bounds_15_16923 : exactInterval 15 16923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16923 : oddCount 16923 15 = 10 ∧ acceleratedOrbit 15 16923 = 30500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16923) = 3 ^ 10 * m + 30500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16923.1, data_15_16923.2]

/-- Complete interval computation for depth 15, residue 16924. -/
theorem bounds_15_16924 : exactInterval 15 16924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16924 : oddCount 16924 15 = 8 ∧ acceleratedOrbit 15 16924 = 3392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16924) = 3 ^ 8 * m + 3392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16924.1, data_15_16924.2]

/-- Complete interval computation for depth 15, residue 16925. -/
theorem bounds_15_16925 : exactInterval 15 16925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16925 : oddCount 16925 15 = 8 ∧ acceleratedOrbit 15 16925 = 3392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16925) = 3 ^ 8 * m + 3392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16925.1, data_15_16925.2]

/-- Complete interval computation for depth 15, residue 16926. -/
theorem bounds_15_16926 : exactInterval 15 16926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16926 : oddCount 16926 15 = 8 ∧ acceleratedOrbit 15 16926 = 3392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16926) = 3 ^ 8 * m + 3392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16926.1, data_15_16926.2]

/-- Complete interval computation for depth 15, residue 16927. -/
theorem bounds_15_16927 : exactInterval 15 16927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16927 : oddCount 16927 15 = 9 ∧ acceleratedOrbit 15 16927 = 10169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16927) = 3 ^ 9 * m + 10169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16927.1, data_15_16927.2]

/-- Complete interval computation for depth 15, residue 16928. -/
theorem bounds_15_16928 : exactInterval 15 16928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16928 : oddCount 16928 15 = 3 ∧ acceleratedOrbit 15 16928 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16928) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16928.1, data_15_16928.2]

/-- Complete interval computation for depth 15, residue 16929. -/
theorem bounds_15_16929 : exactInterval 15 16929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16929 : oddCount 16929 15 = 8 ∧ acceleratedOrbit 15 16929 = 3392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16929) = 3 ^ 8 * m + 3392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16929.1, data_15_16929.2]

/-- Complete interval computation for depth 15, residue 16930. -/
theorem bounds_15_16930 : exactInterval 15 16930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16930 : oddCount 16930 15 = 7 ∧ acceleratedOrbit 15 16930 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16930) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16930.1, data_15_16930.2]

/-- Complete interval computation for depth 15, residue 16931. -/
theorem bounds_15_16931 : exactInterval 15 16931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16931 : oddCount 16931 15 = 7 ∧ acceleratedOrbit 15 16931 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16931) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16931.1, data_15_16931.2]

/-- Complete interval computation for depth 15, residue 16932. -/
theorem bounds_15_16932 : exactInterval 15 16932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16932 : oddCount 16932 15 = 10 ∧ acceleratedOrbit 15 16932 = 30527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16932) = 3 ^ 10 * m + 30527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16932.1, data_15_16932.2]

/-- Complete interval computation for depth 15, residue 16933. -/
theorem bounds_15_16933 : exactInterval 15 16933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16933 : oddCount 16933 15 = 10 ∧ acceleratedOrbit 15 16933 = 30527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16933) = 3 ^ 10 * m + 30527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16933.1, data_15_16933.2]

/-- Complete interval computation for depth 15, residue 16934. -/
theorem bounds_15_16934 : exactInterval 15 16934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16934 : oddCount 16934 15 = 10 ∧ acceleratedOrbit 15 16934 = 30527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16934) = 3 ^ 10 * m + 30527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16934.1, data_15_16934.2]

/-- Complete interval computation for depth 15, residue 16935. -/
theorem bounds_15_16935 : exactInterval 15 16935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16935 : oddCount 16935 15 = 8 ∧ acceleratedOrbit 15 16935 = 3392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16935) = 3 ^ 8 * m + 3392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16935.1, data_15_16935.2]

/-- Complete interval computation for depth 15, residue 16936. -/
theorem bounds_15_16936 : exactInterval 15 16936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16936 : oddCount 16936 15 = 3 ∧ acceleratedOrbit 15 16936 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16936) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16936.1, data_15_16936.2]

/-- Complete interval computation for depth 15, residue 16937. -/
theorem bounds_15_16937 : exactInterval 15 16937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16937 : oddCount 16937 15 = 11 ∧ acceleratedOrbit 15 16937 = 91574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16937) = 3 ^ 11 * m + 91574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16937.1, data_15_16937.2]

/-- Complete interval computation for depth 15, residue 16938. -/
theorem bounds_15_16938 : exactInterval 15 16938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16938 : oddCount 16938 15 = 3 ∧ acceleratedOrbit 15 16938 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16938) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16938.1, data_15_16938.2]

/-- Complete interval computation for depth 15, residue 16939. -/
theorem bounds_15_16939 : exactInterval 15 16939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16939 : oddCount 16939 15 = 7 ∧ acceleratedOrbit 15 16939 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16939) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16939.1, data_15_16939.2]

/-- Complete interval computation for depth 15, residue 16940. -/
theorem bounds_15_16940 : exactInterval 15 16940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16940 : oddCount 16940 15 = 8 ∧ acceleratedOrbit 15 16940 = 3395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16940) = 3 ^ 8 * m + 3395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16940.1, data_15_16940.2]

end Collatz.Research.PassageAtlas.Batch0517
