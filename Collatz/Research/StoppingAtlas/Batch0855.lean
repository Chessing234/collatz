import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0855

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5949. -/
theorem bounds_13_5949 : exactInterval 13 5949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5949 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5949) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5949 : oddCount 5949 13 = 8 ∧ acceleratedOrbit 13 5949 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5949 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5949) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5949.1, data_13_5949.2]

/-- Complete interval computation for depth 13, residue 5950. -/
theorem bounds_13_5950 : exactInterval 13 5950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5950 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5950) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5950 : oddCount 5950 13 = 7 ∧ acceleratedOrbit 13 5950 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5950 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5950) = 3 ^ 7 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5950.1, data_13_5950.2]

/-- Complete interval computation for depth 13, residue 5951. -/
theorem bounds_13_5951 : exactInterval 13 5951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5951 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5951) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5951 : oddCount 5951 13 = 7 ∧ acceleratedOrbit 13 5951 = 1589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5951 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5951) = 3 ^ 7 * m + 1589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5951.1, data_13_5951.2]

/-- Complete interval computation for depth 13, residue 5952. -/
theorem bounds_13_5952 : exactInterval 13 5952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5952 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5952) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5952 : oddCount 5952 13 = 3 ∧ acceleratedOrbit 13 5952 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5952 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5952) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5952.1, data_13_5952.2]

/-- Complete interval computation for depth 13, residue 5953. -/
theorem bounds_13_5953 : exactInterval 13 5953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5953 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5953) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5953 : oddCount 5953 13 = 4 ∧ acceleratedOrbit 13 5953 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5953 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5953) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5953.1, data_13_5953.2]

/-- Complete interval computation for depth 13, residue 5954. -/
theorem bounds_13_5954 : exactInterval 13 5954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5954 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5954) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5954 : oddCount 5954 13 = 7 ∧ acceleratedOrbit 13 5954 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5954 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5954) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5954.1, data_13_5954.2]

/-- Complete interval computation for depth 13, residue 5955. -/
theorem bounds_13_5955 : exactInterval 13 5955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5955 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5955) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5955 : oddCount 5955 13 = 7 ∧ acceleratedOrbit 13 5955 = 1592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5955 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5955) = 3 ^ 7 * m + 1592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5955.1, data_13_5955.2]

/-- Complete interval computation for depth 13, residue 5956. -/
theorem bounds_13_5956 : exactInterval 13 5956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5956 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5956) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5956 : oddCount 5956 13 = 4 ∧ acceleratedOrbit 13 5956 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5956 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5956) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5956.1, data_13_5956.2]

/-- Complete interval computation for depth 13, residue 5957. -/
theorem bounds_13_5957 : exactInterval 13 5957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5957 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5957) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5957 : oddCount 5957 13 = 4 ∧ acceleratedOrbit 13 5957 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5957 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5957) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5957.1, data_13_5957.2]

/-- Complete interval computation for depth 13, residue 5958. -/
theorem bounds_13_5958 : exactInterval 13 5958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5958 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5958) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5958 : oddCount 5958 13 = 4 ∧ acceleratedOrbit 13 5958 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5958 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5958) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5958.1, data_13_5958.2]

/-- Complete interval computation for depth 13, residue 5959. -/
theorem bounds_13_5959 : exactInterval 13 5959 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5959 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5959) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5959 : oddCount 5959 13 = 8 ∧ acceleratedOrbit 13 5959 = 4774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5959 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5959) = 3 ^ 8 * m + 4774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5959.1, data_13_5959.2]

/-- Complete interval computation for depth 13, residue 5960. -/
theorem bounds_13_5960 : exactInterval 13 5960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5960 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5960) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5960 : oddCount 5960 13 = 7 ∧ acceleratedOrbit 13 5960 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5960 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5960) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5960.1, data_13_5960.2]

/-- Complete interval computation for depth 13, residue 5961. -/
theorem bounds_13_5961 : exactInterval 13 5961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5961 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5961) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5961 : oddCount 5961 13 = 8 ∧ acceleratedOrbit 13 5961 = 4778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5961 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5961) = 3 ^ 8 * m + 4778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5961.1, data_13_5961.2]

/-- Complete interval computation for depth 13, residue 5962. -/
theorem bounds_13_5962 : exactInterval 13 5962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5962 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5962) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5962 : oddCount 5962 13 = 7 ∧ acceleratedOrbit 13 5962 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5962 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5962) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5962.1, data_13_5962.2]

/-- Complete interval computation for depth 13, residue 5963. -/
theorem bounds_13_5963 : exactInterval 13 5963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5963 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5963) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5963 : oddCount 5963 13 = 4 ∧ acceleratedOrbit 13 5963 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5963 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5963) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5963.1, data_13_5963.2]

end Collatz.Research.StoppingAtlas.Batch0855
