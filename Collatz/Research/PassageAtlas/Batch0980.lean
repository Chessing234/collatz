import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0980

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32079. -/
theorem bounds_15_32079 : exactInterval 15 32079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32079 : oddCount 32079 15 = 9 ∧ acceleratedOrbit 15 32079 = 19271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32079) = 3 ^ 9 * m + 19271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32079.1, data_15_32079.2]

/-- Complete interval computation for depth 15, residue 32080. -/
theorem bounds_15_32080 : exactInterval 15 32080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32080 : oddCount 32080 15 = 5 ∧ acceleratedOrbit 15 32080 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32080) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32080.1, data_15_32080.2]

/-- Complete interval computation for depth 15, residue 32081. -/
theorem bounds_15_32081 : exactInterval 15 32081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32081 : oddCount 32081 15 = 9 ∧ acceleratedOrbit 15 32081 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32081) = 3 ^ 9 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32081.1, data_15_32081.2]

/-- Complete interval computation for depth 15, residue 32082. -/
theorem bounds_15_32082 : exactInterval 15 32082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32082 : oddCount 32082 15 = 12 ∧ acceleratedOrbit 15 32082 = 520370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32082) = 3 ^ 12 * m + 520370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32082.1, data_15_32082.2]

/-- Complete interval computation for depth 15, residue 32083. -/
theorem bounds_15_32083 : exactInterval 15 32083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32083 : oddCount 32083 15 = 12 ∧ acceleratedOrbit 15 32083 = 520370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32083) = 3 ^ 12 * m + 520370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32083.1, data_15_32083.2]

/-- Complete interval computation for depth 15, residue 32084. -/
theorem bounds_15_32084 : exactInterval 15 32084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32084 : oddCount 32084 15 = 5 ∧ acceleratedOrbit 15 32084 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32084) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32084.1, data_15_32084.2]

/-- Complete interval computation for depth 15, residue 32085. -/
theorem bounds_15_32085 : exactInterval 15 32085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32085 : oddCount 32085 15 = 5 ∧ acceleratedOrbit 15 32085 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32085) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32085.1, data_15_32085.2]

/-- Complete interval computation for depth 15, residue 32086. -/
theorem bounds_15_32086 : exactInterval 15 32086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32086 : oddCount 32086 15 = 10 ∧ acceleratedOrbit 15 32086 = 57833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32086) = 3 ^ 10 * m + 57833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32086.1, data_15_32086.2]

/-- Complete interval computation for depth 15, residue 32087. -/
theorem bounds_15_32087 : exactInterval 15 32087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32087 : oddCount 32087 15 = 10 ∧ acceleratedOrbit 15 32087 = 57833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32087) = 3 ^ 10 * m + 57833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32087.1, data_15_32087.2]

/-- Complete interval computation for depth 15, residue 32088. -/
theorem bounds_15_32088 : exactInterval 15 32088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32088 : oddCount 32088 15 = 7 ∧ acceleratedOrbit 15 32088 = 2143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32088) = 3 ^ 7 * m + 2143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32088.1, data_15_32088.2]

/-- Complete interval computation for depth 15, residue 32089. -/
theorem bounds_15_32089 : exactInterval 15 32089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32089 : oddCount 32089 15 = 5 ∧ acceleratedOrbit 15 32089 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32089) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32089.1, data_15_32089.2]

/-- Complete interval computation for depth 15, residue 32090. -/
theorem bounds_15_32090 : exactInterval 15 32090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32090 : oddCount 32090 15 = 7 ∧ acceleratedOrbit 15 32090 = 2143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32090) = 3 ^ 7 * m + 2143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32090.1, data_15_32090.2]

/-- Complete interval computation for depth 15, residue 32091. -/
theorem bounds_15_32091 : exactInterval 15 32091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32091 : oddCount 32091 15 = 11 ∧ acceleratedOrbit 15 32091 = 173501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32091) = 3 ^ 11 * m + 173501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32091.1, data_15_32091.2]

/-- Complete interval computation for depth 15, residue 32092. -/
theorem bounds_15_32092 : exactInterval 15 32092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32092 : oddCount 32092 15 = 7 ∧ acceleratedOrbit 15 32092 = 2143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32092) = 3 ^ 7 * m + 2143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32092.1, data_15_32092.2]

/-- Complete interval computation for depth 15, residue 32093. -/
theorem bounds_15_32093 : exactInterval 15 32093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32093 : oddCount 32093 15 = 7 ∧ acceleratedOrbit 15 32093 = 2143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32093) = 3 ^ 7 * m + 2143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32093.1, data_15_32093.2]

/-- Complete interval computation for depth 15, residue 32094. -/
theorem bounds_15_32094 : exactInterval 15 32094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32094 : oddCount 32094 15 = 8 ∧ acceleratedOrbit 15 32094 = 6427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32094) = 3 ^ 8 * m + 6427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32094.1, data_15_32094.2]

/-- Complete interval computation for depth 15, residue 32095. -/
theorem bounds_15_32095 : exactInterval 15 32095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32095 : oddCount 32095 15 = 8 ∧ acceleratedOrbit 15 32095 = 6427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32095) = 3 ^ 8 * m + 6427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32095.1, data_15_32095.2]

/-- Complete interval computation for depth 15, residue 32096. -/
theorem bounds_15_32096 : exactInterval 15 32096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32096 : oddCount 32096 15 = 7 ∧ acceleratedOrbit 15 32096 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32096) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32096.1, data_15_32096.2]

/-- Complete interval computation for depth 15, residue 32097. -/
theorem bounds_15_32097 : exactInterval 15 32097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32097 : oddCount 32097 15 = 8 ∧ acceleratedOrbit 15 32097 = 6428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32097) = 3 ^ 8 * m + 6428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32097.1, data_15_32097.2]

/-- Complete interval computation for depth 15, residue 32098. -/
theorem bounds_15_32098 : exactInterval 15 32098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32098 : oddCount 32098 15 = 6 ∧ acceleratedOrbit 15 32098 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32098) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32098.1, data_15_32098.2]

/-- Complete interval computation for depth 15, residue 32099. -/
theorem bounds_15_32099 : exactInterval 15 32099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32099 : oddCount 32099 15 = 6 ∧ acceleratedOrbit 15 32099 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32099) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32099.1, data_15_32099.2]

/-- Complete interval computation for depth 15, residue 32100. -/
theorem bounds_15_32100 : exactInterval 15 32100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32100 : oddCount 32100 15 = 6 ∧ acceleratedOrbit 15 32100 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32100) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32100.1, data_15_32100.2]

/-- Complete interval computation for depth 15, residue 32101. -/
theorem bounds_15_32101 : exactInterval 15 32101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32101 : oddCount 32101 15 = 6 ∧ acceleratedOrbit 15 32101 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32101) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32101.1, data_15_32101.2]

/-- Complete interval computation for depth 15, residue 32102. -/
theorem bounds_15_32102 : exactInterval 15 32102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32102 : oddCount 32102 15 = 6 ∧ acceleratedOrbit 15 32102 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32102) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32102.1, data_15_32102.2]

/-- Complete interval computation for depth 15, residue 32103. -/
theorem bounds_15_32103 : exactInterval 15 32103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32103 : oddCount 32103 15 = 10 ∧ acceleratedOrbit 15 32103 = 57853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32103) = 3 ^ 10 * m + 57853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32103.1, data_15_32103.2]

/-- Complete interval computation for depth 15, residue 32104. -/
theorem bounds_15_32104 : exactInterval 15 32104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32104 : oddCount 32104 15 = 7 ∧ acceleratedOrbit 15 32104 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32104) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32104.1, data_15_32104.2]

/-- Complete interval computation for depth 15, residue 32105. -/
theorem bounds_15_32105 : exactInterval 15 32105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32105 : oddCount 32105 15 = 7 ∧ acceleratedOrbit 15 32105 = 2143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32105) = 3 ^ 7 * m + 2143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32105.1, data_15_32105.2]

/-- Complete interval computation for depth 15, residue 32106. -/
theorem bounds_15_32106 : exactInterval 15 32106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32106 : oddCount 32106 15 = 7 ∧ acceleratedOrbit 15 32106 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32106) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32106.1, data_15_32106.2]

/-- Complete interval computation for depth 15, residue 32107. -/
theorem bounds_15_32107 : exactInterval 15 32107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32107 : oddCount 32107 15 = 9 ∧ acceleratedOrbit 15 32107 = 19288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32107) = 3 ^ 9 * m + 19288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32107.1, data_15_32107.2]

/-- Complete interval computation for depth 15, residue 32108. -/
theorem bounds_15_32108 : exactInterval 15 32108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32108 : oddCount 32108 15 = 9 ∧ acceleratedOrbit 15 32108 = 19291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32108) = 3 ^ 9 * m + 19291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32108.1, data_15_32108.2]

/-- Complete interval computation for depth 15, residue 32109. -/
theorem bounds_15_32109 : exactInterval 15 32109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32109 : oddCount 32109 15 = 9 ∧ acceleratedOrbit 15 32109 = 19291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32109) = 3 ^ 9 * m + 19291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32109.1, data_15_32109.2]

/-- Complete interval computation for depth 15, residue 32110. -/
theorem bounds_15_32110 : exactInterval 15 32110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32110 : oddCount 32110 15 = 9 ∧ acceleratedOrbit 15 32110 = 19291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32110) = 3 ^ 9 * m + 19291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32110.1, data_15_32110.2]

/-- Complete interval computation for depth 15, residue 32111. -/
theorem bounds_15_32111 : exactInterval 15 32111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32111 : oddCount 32111 15 = 8 ∧ acceleratedOrbit 15 32111 = 6430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32111) = 3 ^ 8 * m + 6430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32111.1, data_15_32111.2]

end Collatz.Research.PassageAtlas.Batch0980
