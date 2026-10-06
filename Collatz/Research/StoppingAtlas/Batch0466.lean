import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0466

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 4070. -/
theorem bounds_12_4070 : exactInterval 12 4070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4070 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4070) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4070 : oddCount 4070 12 = 7 ∧ acceleratedOrbit 12 4070 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4070 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4070) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4070.1, data_12_4070.2]

/-- Complete interval computation for depth 12, residue 4071. -/
theorem bounds_12_4071 : exactInterval 12 4071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4071 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4071) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4071 : oddCount 4071 12 = 8 ∧ acceleratedOrbit 12 4071 = 6524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4071 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4071) = 3 ^ 8 * m + 6524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4071.1, data_12_4071.2]

/-- Complete interval computation for depth 12, residue 4072. -/
theorem bounds_12_4072 : exactInterval 12 4072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4072 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4072) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4072 : oddCount 4072 12 = 7 ∧ acceleratedOrbit 12 4072 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4072 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4072) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4072.1, data_12_4072.2]

/-- Complete interval computation for depth 12, residue 4073. -/
theorem bounds_12_4073 : exactInterval 12 4073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4073 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4073) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4073 : oddCount 4073 12 = 8 ∧ acceleratedOrbit 12 4073 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4073 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4073) = 3 ^ 8 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4073.1, data_12_4073.2]

/-- Complete interval computation for depth 12, residue 4074. -/
theorem bounds_12_4074 : exactInterval 12 4074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4074 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4074) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4074 : oddCount 4074 12 = 7 ∧ acceleratedOrbit 12 4074 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4074 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4074) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4074.1, data_12_4074.2]

/-- Complete interval computation for depth 12, residue 4075. -/
theorem bounds_12_4075 : exactInterval 12 4075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4075 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4075) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4075 : oddCount 4075 12 = 9 ∧ acceleratedOrbit 12 4075 = 19592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4075 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4075) = 3 ^ 9 * m + 19592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4075.1, data_12_4075.2]

/-- Complete interval computation for depth 12, residue 4076. -/
theorem bounds_12_4076 : exactInterval 12 4076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4076 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4076) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4076 : oddCount 4076 12 = 7 ∧ acceleratedOrbit 12 4076 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4076 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4076) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4076.1, data_12_4076.2]

/-- Complete interval computation for depth 12, residue 4077. -/
theorem bounds_12_4077 : exactInterval 12 4077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4077 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4077) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4077 : oddCount 4077 12 = 7 ∧ acceleratedOrbit 12 4077 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4077 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4077) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4077.1, data_12_4077.2]

/-- Complete interval computation for depth 12, residue 4078. -/
theorem bounds_12_4078 : exactInterval 12 4078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4078 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4078) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4078 : oddCount 4078 12 = 7 ∧ acceleratedOrbit 12 4078 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4078 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4078) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4078.1, data_12_4078.2]

/-- Complete interval computation for depth 12, residue 4079. -/
theorem bounds_12_4079 : exactInterval 12 4079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4079 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4079) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4079 : oddCount 4079 12 = 8 ∧ acceleratedOrbit 12 4079 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4079 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4079) = 3 ^ 8 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4079.1, data_12_4079.2]

/-- Complete interval computation for depth 12, residue 4080. -/
theorem bounds_12_4080 : exactInterval 12 4080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4080 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4080) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4080 : oddCount 4080 12 = 8 ∧ acceleratedOrbit 12 4080 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4080 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4080) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4080.1, data_12_4080.2]

/-- Complete interval computation for depth 12, residue 4081. -/
theorem bounds_12_4081 : exactInterval 12 4081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4081 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4081) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4081 : oddCount 4081 12 = 7 ∧ acceleratedOrbit 12 4081 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4081 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4081) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4081.1, data_12_4081.2]

/-- Complete interval computation for depth 12, residue 4082. -/
theorem bounds_12_4082 : exactInterval 12 4082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4082 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4082) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4082 : oddCount 4082 12 = 7 ∧ acceleratedOrbit 12 4082 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4082 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4082) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4082.1, data_12_4082.2]

/-- Complete interval computation for depth 12, residue 4083. -/
theorem bounds_12_4083 : exactInterval 12 4083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4083 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4083) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4083 : oddCount 4083 12 = 7 ∧ acceleratedOrbit 12 4083 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4083 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4083) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4083.1, data_12_4083.2]

/-- Complete interval computation for depth 12, residue 4084. -/
theorem bounds_12_4084 : exactInterval 12 4084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4084 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4084) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4084 : oddCount 4084 12 = 8 ∧ acceleratedOrbit 12 4084 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4084 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4084) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4084.1, data_12_4084.2]

end Collatz.Research.StoppingAtlas.Batch0466
