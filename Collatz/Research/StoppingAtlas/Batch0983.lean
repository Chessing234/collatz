import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0983

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7915. -/
theorem bounds_13_7915 : exactInterval 13 7915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7915 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7915) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7915 : oddCount 7915 13 = 7 ∧ acceleratedOrbit 13 7915 = 2114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7915 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7915) = 3 ^ 7 * m + 2114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7915.1, data_13_7915.2]

/-- Complete interval computation for depth 13, residue 7916. -/
theorem bounds_13_7916 : exactInterval 13 7916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7916 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7916) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7916 : oddCount 7916 13 = 5 ∧ acceleratedOrbit 13 7916 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7916 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7916) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7916.1, data_13_7916.2]

/-- Complete interval computation for depth 13, residue 7917. -/
theorem bounds_13_7917 : exactInterval 13 7917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7917 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7917) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7917 : oddCount 7917 13 = 5 ∧ acceleratedOrbit 13 7917 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7917 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7917) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7917.1, data_13_7917.2]

/-- Complete interval computation for depth 13, residue 7918. -/
theorem bounds_13_7918 : exactInterval 13 7918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7918 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7918) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7918 : oddCount 7918 13 = 5 ∧ acceleratedOrbit 13 7918 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7918 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7918) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7918.1, data_13_7918.2]

/-- Complete interval computation for depth 13, residue 7919. -/
theorem bounds_13_7919 : exactInterval 13 7919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7919 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7919) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7919 : oddCount 7919 13 = 9 ∧ acceleratedOrbit 13 7919 = 19030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7919 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7919) = 3 ^ 9 * m + 19030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7919.1, data_13_7919.2]

/-- Complete interval computation for depth 13, residue 7920. -/
theorem bounds_13_7920 : exactInterval 13 7920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7920 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7920) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7920 : oddCount 7920 13 = 7 ∧ acceleratedOrbit 13 7920 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7920 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7920) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7920.1, data_13_7920.2]

/-- Complete interval computation for depth 13, residue 7921. -/
theorem bounds_13_7921 : exactInterval 13 7921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7921 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7921) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7921 : oddCount 7921 13 = 5 ∧ acceleratedOrbit 13 7921 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7921 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7921) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7921.1, data_13_7921.2]

/-- Complete interval computation for depth 13, residue 7922. -/
theorem bounds_13_7922 : exactInterval 13 7922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7922 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7922) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7922 : oddCount 7922 13 = 7 ∧ acceleratedOrbit 13 7922 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7922 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7922) = 3 ^ 7 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7922.1, data_13_7922.2]

/-- Complete interval computation for depth 13, residue 7923. -/
theorem bounds_13_7923 : exactInterval 13 7923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7923 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7923) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7923 : oddCount 7923 13 = 7 ∧ acceleratedOrbit 13 7923 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7923 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7923) = 3 ^ 7 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7923.1, data_13_7923.2]

/-- Complete interval computation for depth 13, residue 7924. -/
theorem bounds_13_7924 : exactInterval 13 7924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7924 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7924) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7924 : oddCount 7924 13 = 7 ∧ acceleratedOrbit 13 7924 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7924 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7924) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7924.1, data_13_7924.2]

/-- Complete interval computation for depth 13, residue 7925. -/
theorem bounds_13_7925 : exactInterval 13 7925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7925 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7925) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7925 : oddCount 7925 13 = 7 ∧ acceleratedOrbit 13 7925 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7925 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7925) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7925.1, data_13_7925.2]

/-- Complete interval computation for depth 13, residue 7926. -/
theorem bounds_13_7926 : exactInterval 13 7926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7926 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7926) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7926 : oddCount 7926 13 = 7 ∧ acceleratedOrbit 13 7926 = 2117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7926 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7926) = 3 ^ 7 * m + 2117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7926.1, data_13_7926.2]

/-- Complete interval computation for depth 13, residue 7927. -/
theorem bounds_13_7927 : exactInterval 13 7927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7927 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7927) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7927 : oddCount 7927 13 = 7 ∧ acceleratedOrbit 13 7927 = 2117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7927 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7927) = 3 ^ 7 * m + 2117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7927.1, data_13_7927.2]

/-- Complete interval computation for depth 13, residue 7928. -/
theorem bounds_13_7928 : exactInterval 13 7928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7928 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7928) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7928 : oddCount 7928 13 = 7 ∧ acceleratedOrbit 13 7928 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7928 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7928) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7928.1, data_13_7928.2]

/-- Complete interval computation for depth 13, residue 7929. -/
theorem bounds_13_7929 : exactInterval 13 7929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7929 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7929) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7929 : oddCount 7929 13 = 6 ∧ acceleratedOrbit 13 7929 = 706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7929 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7929) = 3 ^ 6 * m + 706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7929.1, data_13_7929.2]

end Collatz.Research.StoppingAtlas.Batch0983
