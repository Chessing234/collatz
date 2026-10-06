import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0920

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6947. -/
theorem bounds_13_6947 : exactInterval 13 6947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6947 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6947) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6947 : oddCount 6947 13 = 6 ∧ acceleratedOrbit 13 6947 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6947 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6947) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6947.1, data_13_6947.2]

/-- Complete interval computation for depth 13, residue 6948. -/
theorem bounds_13_6948 : exactInterval 13 6948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6948 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6948) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6948 : oddCount 6948 13 = 6 ∧ acceleratedOrbit 13 6948 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6948 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6948) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6948.1, data_13_6948.2]

/-- Complete interval computation for depth 13, residue 6949. -/
theorem bounds_13_6949 : exactInterval 13 6949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6949 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6949) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6949 : oddCount 6949 13 = 6 ∧ acceleratedOrbit 13 6949 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6949 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6949) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6949.1, data_13_6949.2]

/-- Complete interval computation for depth 13, residue 6950. -/
theorem bounds_13_6950 : exactInterval 13 6950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6950 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6950) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6950 : oddCount 6950 13 = 6 ∧ acceleratedOrbit 13 6950 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6950 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6950) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6950.1, data_13_6950.2]

/-- Complete interval computation for depth 13, residue 6951. -/
theorem bounds_13_6951 : exactInterval 13 6951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6951 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6951) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6951 : oddCount 6951 13 = 9 ∧ acceleratedOrbit 13 6951 = 16706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6951 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6951) = 3 ^ 9 * m + 16706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6951.1, data_13_6951.2]

/-- Complete interval computation for depth 13, residue 6952. -/
theorem bounds_13_6952 : exactInterval 13 6952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6952 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6952) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6952 : oddCount 6952 13 = 3 ∧ acceleratedOrbit 13 6952 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6952 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6952) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6952.1, data_13_6952.2]

/-- Complete interval computation for depth 13, residue 6953. -/
theorem bounds_13_6953 : exactInterval 13 6953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6953 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6953) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6953 : oddCount 6953 13 = 9 ∧ acceleratedOrbit 13 6953 = 16712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6953 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6953) = 3 ^ 9 * m + 16712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6953.1, data_13_6953.2]

/-- Complete interval computation for depth 13, residue 6954. -/
theorem bounds_13_6954 : exactInterval 13 6954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6954 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6954) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6954 : oddCount 6954 13 = 3 ∧ acceleratedOrbit 13 6954 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6954 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6954) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6954.1, data_13_6954.2]

/-- Complete interval computation for depth 13, residue 6955. -/
theorem bounds_13_6955 : exactInterval 13 6955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6955 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6955) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6955 : oddCount 6955 13 = 7 ∧ acceleratedOrbit 13 6955 = 1858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6955 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6955) = 3 ^ 7 * m + 1858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6955.1, data_13_6955.2]

/-- Complete interval computation for depth 13, residue 6956. -/
theorem bounds_13_6956 : exactInterval 13 6956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6956 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6956) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6956 : oddCount 6956 13 = 7 ∧ acceleratedOrbit 13 6956 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6956 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6956) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6956.1, data_13_6956.2]

/-- Complete interval computation for depth 13, residue 6957. -/
theorem bounds_13_6957 : exactInterval 13 6957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6957 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6957) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6957 : oddCount 6957 13 = 7 ∧ acceleratedOrbit 13 6957 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6957 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6957) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6957.1, data_13_6957.2]

/-- Complete interval computation for depth 13, residue 6958. -/
theorem bounds_13_6958 : exactInterval 13 6958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6958 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6958) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6958 : oddCount 6958 13 = 7 ∧ acceleratedOrbit 13 6958 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6958 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6958) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6958.1, data_13_6958.2]

/-- Complete interval computation for depth 13, residue 6959. -/
theorem bounds_13_6959 : exactInterval 13 6959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6959 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6959) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6959 : oddCount 6959 13 = 8 ∧ acceleratedOrbit 13 6959 = 5575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6959 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6959) = 3 ^ 8 * m + 5575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6959.1, data_13_6959.2]

/-- Complete interval computation for depth 13, residue 6960. -/
theorem bounds_13_6960 : exactInterval 13 6960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6960 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6960) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6960 : oddCount 6960 13 = 3 ∧ acceleratedOrbit 13 6960 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6960 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6960) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6960.1, data_13_6960.2]

/-- Complete interval computation for depth 13, residue 6961. -/
theorem bounds_13_6961 : exactInterval 13 6961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6961 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6961) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6961 : oddCount 6961 13 = 7 ∧ acceleratedOrbit 13 6961 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6961 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6961) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6961.1, data_13_6961.2]

/-- Complete interval computation for depth 13, residue 6962. -/
theorem bounds_13_6962 : exactInterval 13 6962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6962 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6962) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6962 : oddCount 6962 13 = 7 ∧ acceleratedOrbit 13 6962 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6962 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6962) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6962.1, data_13_6962.2]

end Collatz.Research.StoppingAtlas.Batch0920
