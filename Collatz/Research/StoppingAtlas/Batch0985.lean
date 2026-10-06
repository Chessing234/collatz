import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0985

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7946. -/
theorem bounds_13_7946 : exactInterval 13 7946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7946 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7946) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7946 : oddCount 7946 13 = 7 ∧ acceleratedOrbit 13 7946 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7946 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7946) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7946.1, data_13_7946.2]

/-- Complete interval computation for depth 13, residue 7947. -/
theorem bounds_13_7947 : exactInterval 13 7947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7947 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7947) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7947 : oddCount 7947 13 = 7 ∧ acceleratedOrbit 13 7947 = 2123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7947 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7947) = 3 ^ 7 * m + 2123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7947.1, data_13_7947.2]

/-- Complete interval computation for depth 13, residue 7948. -/
theorem bounds_13_7948 : exactInterval 13 7948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7948 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7948) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7948 : oddCount 7948 13 = 7 ∧ acceleratedOrbit 13 7948 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7948 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7948) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7948.1, data_13_7948.2]

/-- Complete interval computation for depth 13, residue 7949. -/
theorem bounds_13_7949 : exactInterval 13 7949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7949 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7949) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7949 : oddCount 7949 13 = 7 ∧ acceleratedOrbit 13 7949 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7949 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7949) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7949.1, data_13_7949.2]

/-- Complete interval computation for depth 13, residue 7950. -/
theorem bounds_13_7950 : exactInterval 13 7950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7950 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7950) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7950 : oddCount 7950 13 = 5 ∧ acceleratedOrbit 13 7950 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7950 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7950) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7950.1, data_13_7950.2]

/-- Complete interval computation for depth 13, residue 7951. -/
theorem bounds_13_7951 : exactInterval 13 7951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7951 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7951) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7951 : oddCount 7951 13 = 5 ∧ acceleratedOrbit 13 7951 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7951 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7951) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7951.1, data_13_7951.2]

/-- Complete interval computation for depth 13, residue 7952. -/
theorem bounds_13_7952 : exactInterval 13 7952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7952 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7952) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7952 : oddCount 7952 13 = 4 ∧ acceleratedOrbit 13 7952 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7952 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7952) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7952.1, data_13_7952.2]

/-- Complete interval computation for depth 13, residue 7953. -/
theorem bounds_13_7953 : exactInterval 13 7953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7953 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7953) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7953 : oddCount 7953 13 = 7 ∧ acceleratedOrbit 13 7953 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7953 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7953) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7953.1, data_13_7953.2]

/-- Complete interval computation for depth 13, residue 7954. -/
theorem bounds_13_7954 : exactInterval 13 7954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7954 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7954) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7954 : oddCount 7954 13 = 8 ∧ acceleratedOrbit 13 7954 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7954 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7954) = 3 ^ 8 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7954.1, data_13_7954.2]

/-- Complete interval computation for depth 13, residue 7955. -/
theorem bounds_13_7955 : exactInterval 13 7955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7955 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7955) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7955 : oddCount 7955 13 = 8 ∧ acceleratedOrbit 13 7955 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7955 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7955) = 3 ^ 8 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7955.1, data_13_7955.2]

/-- Complete interval computation for depth 13, residue 7956. -/
theorem bounds_13_7956 : exactInterval 13 7956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7956 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7956) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7956 : oddCount 7956 13 = 4 ∧ acceleratedOrbit 13 7956 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7956 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7956) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7956.1, data_13_7956.2]

/-- Complete interval computation for depth 13, residue 7957. -/
theorem bounds_13_7957 : exactInterval 13 7957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7957 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7957) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7957 : oddCount 7957 13 = 4 ∧ acceleratedOrbit 13 7957 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7957 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7957) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7957.1, data_13_7957.2]

/-- Complete interval computation for depth 13, residue 7958. -/
theorem bounds_13_7958 : exactInterval 13 7958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7958 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7958) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7958 : oddCount 7958 13 = 7 ∧ acceleratedOrbit 13 7958 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7958 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7958) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7958.1, data_13_7958.2]

/-- Complete interval computation for depth 13, residue 7959. -/
theorem bounds_13_7959 : exactInterval 13 7959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7959 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7959) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7959 : oddCount 7959 13 = 7 ∧ acceleratedOrbit 13 7959 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7959 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7959) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7959.1, data_13_7959.2]

/-- Complete interval computation for depth 13, residue 7960. -/
theorem bounds_13_7960 : exactInterval 13 7960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7960 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7960) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7960 : oddCount 7960 13 = 4 ∧ acceleratedOrbit 13 7960 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7960 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7960) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7960.1, data_13_7960.2]

end Collatz.Research.StoppingAtlas.Batch0985
