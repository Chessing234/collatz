import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0401

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3072. -/
theorem bounds_12_3072 : exactInterval 12 3072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3072 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3072) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3072 : oddCount 3072 12 = 2 ∧ acceleratedOrbit 12 3072 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3072 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3072) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3072.1, data_12_3072.2]

/-- Complete interval computation for depth 12, residue 3073. -/
theorem bounds_12_3073 : exactInterval 12 3073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3073 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3073) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3073 : oddCount 3073 12 = 6 ∧ acceleratedOrbit 12 3073 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3073 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3073) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3073.1, data_12_3073.2]

/-- Complete interval computation for depth 12, residue 3074. -/
theorem bounds_12_3074 : exactInterval 12 3074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3074 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3074) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3074 : oddCount 3074 12 = 7 ∧ acceleratedOrbit 12 3074 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3074 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3074) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3074.1, data_12_3074.2]

/-- Complete interval computation for depth 12, residue 3075. -/
theorem bounds_12_3075 : exactInterval 12 3075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3075 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3075) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3075 : oddCount 3075 12 = 7 ∧ acceleratedOrbit 12 3075 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3075 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3075) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3075.1, data_12_3075.2]

/-- Complete interval computation for depth 12, residue 3076. -/
theorem bounds_12_3076 : exactInterval 12 3076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3076 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3076) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3076 : oddCount 3076 12 = 4 ∧ acceleratedOrbit 12 3076 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3076 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3076) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3076.1, data_12_3076.2]

/-- Complete interval computation for depth 12, residue 3077. -/
theorem bounds_12_3077 : exactInterval 12 3077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3077 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3077) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3077 : oddCount 3077 12 = 4 ∧ acceleratedOrbit 12 3077 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3077 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3077) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3077.1, data_12_3077.2]

/-- Complete interval computation for depth 12, residue 3078. -/
theorem bounds_12_3078 : exactInterval 12 3078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3078 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3078) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3078 : oddCount 3078 12 = 4 ∧ acceleratedOrbit 12 3078 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3078 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3078) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3078.1, data_12_3078.2]

/-- Complete interval computation for depth 12, residue 3079. -/
theorem bounds_12_3079 : exactInterval 12 3079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3079 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3079) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3079 : oddCount 3079 12 = 7 ∧ acceleratedOrbit 12 3079 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3079 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3079) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3079.1, data_12_3079.2]

/-- Complete interval computation for depth 12, residue 3080. -/
theorem bounds_12_3080 : exactInterval 12 3080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3080 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3080) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3080 : oddCount 3080 12 = 5 ∧ acceleratedOrbit 12 3080 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3080 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3080) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3080.1, data_12_3080.2]

/-- Complete interval computation for depth 12, residue 3081. -/
theorem bounds_12_3081 : exactInterval 12 3081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3081 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3081) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3081 : oddCount 3081 12 = 8 ∧ acceleratedOrbit 12 3081 = 4940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3081 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3081) = 3 ^ 8 * m + 4940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3081.1, data_12_3081.2]

/-- Complete interval computation for depth 12, residue 3082. -/
theorem bounds_12_3082 : exactInterval 12 3082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3082 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3082) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3082 : oddCount 3082 12 = 5 ∧ acceleratedOrbit 12 3082 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3082 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3082) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3082.1, data_12_3082.2]

/-- Complete interval computation for depth 12, residue 3083. -/
theorem bounds_12_3083 : exactInterval 12 3083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3083 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3083) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3083 : oddCount 3083 12 = 4 ∧ acceleratedOrbit 12 3083 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3083 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3083) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3083.1, data_12_3083.2]

/-- Complete interval computation for depth 12, residue 3084. -/
theorem bounds_12_3084 : exactInterval 12 3084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3084 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3084) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3084 : oddCount 3084 12 = 5 ∧ acceleratedOrbit 12 3084 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3084 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3084) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3084.1, data_12_3084.2]

/-- Complete interval computation for depth 12, residue 3085. -/
theorem bounds_12_3085 : exactInterval 12 3085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3085 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3085) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3085 : oddCount 3085 12 = 5 ∧ acceleratedOrbit 12 3085 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3085 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3085) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3085.1, data_12_3085.2]

/-- Complete interval computation for depth 12, residue 3086. -/
theorem bounds_12_3086 : exactInterval 12 3086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3086 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3086) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3086 : oddCount 3086 12 = 6 ∧ acceleratedOrbit 12 3086 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3086 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3086) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3086.1, data_12_3086.2]

end Collatz.Research.StoppingAtlas.Batch0401
