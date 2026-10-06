import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0733

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4075. -/
theorem bounds_13_4075 : exactInterval 13 4075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4075 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4075) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4075 : oddCount 4075 13 = 9 ∧ acceleratedOrbit 13 4075 = 9796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4075 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4075) = 3 ^ 9 * m + 9796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4075.1, data_13_4075.2]

/-- Complete interval computation for depth 13, residue 4076. -/
theorem bounds_13_4076 : exactInterval 13 4076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4076 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4076) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4076 : oddCount 4076 13 = 7 ∧ acceleratedOrbit 13 4076 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4076 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4076) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4076.1, data_13_4076.2]

/-- Complete interval computation for depth 13, residue 4077. -/
theorem bounds_13_4077 : exactInterval 13 4077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4077 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4077) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4077 : oddCount 4077 13 = 7 ∧ acceleratedOrbit 13 4077 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4077 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4077) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4077.1, data_13_4077.2]

/-- Complete interval computation for depth 13, residue 4078. -/
theorem bounds_13_4078 : exactInterval 13 4078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4078 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4078) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4078 : oddCount 4078 13 = 7 ∧ acceleratedOrbit 13 4078 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4078 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4078) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4078.1, data_13_4078.2]

/-- Complete interval computation for depth 13, residue 4079. -/
theorem bounds_13_4079 : exactInterval 13 4079 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4079 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4079) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4079 : oddCount 4079 13 = 8 ∧ acceleratedOrbit 13 4079 = 3268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4079 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4079) = 3 ^ 8 * m + 3268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4079.1, data_13_4079.2]

/-- Complete interval computation for depth 13, residue 4080. -/
theorem bounds_13_4080 : exactInterval 13 4080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4080 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4080) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4080 : oddCount 4080 13 = 8 ∧ acceleratedOrbit 13 4080 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4080 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4080) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4080.1, data_13_4080.2]

/-- Complete interval computation for depth 13, residue 4081. -/
theorem bounds_13_4081 : exactInterval 13 4081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4081 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4081) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4081 : oddCount 4081 13 = 7 ∧ acceleratedOrbit 13 4081 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4081 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4081) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4081.1, data_13_4081.2]

/-- Complete interval computation for depth 13, residue 4082. -/
theorem bounds_13_4082 : exactInterval 13 4082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4082 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4082) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4082 : oddCount 4082 13 = 7 ∧ acceleratedOrbit 13 4082 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4082 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4082) = 3 ^ 7 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4082.1, data_13_4082.2]

/-- Complete interval computation for depth 13, residue 4083. -/
theorem bounds_13_4083 : exactInterval 13 4083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4083 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4083) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4083 : oddCount 4083 13 = 7 ∧ acceleratedOrbit 13 4083 = 1091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4083 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4083) = 3 ^ 7 * m + 1091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4083.1, data_13_4083.2]

/-- Complete interval computation for depth 13, residue 4084. -/
theorem bounds_13_4084 : exactInterval 13 4084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4084 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4084) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4084 : oddCount 4084 13 = 8 ∧ acceleratedOrbit 13 4084 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4084 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4084) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4084.1, data_13_4084.2]

/-- Complete interval computation for depth 13, residue 4085. -/
theorem bounds_13_4085 : exactInterval 13 4085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4085 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4085) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4085 : oddCount 4085 13 = 8 ∧ acceleratedOrbit 13 4085 = 3280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4085 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4085) = 3 ^ 8 * m + 3280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4085.1, data_13_4085.2]

/-- Complete interval computation for depth 13, residue 4086. -/
theorem bounds_13_4086 : exactInterval 13 4086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4086 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4086) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4086 : oddCount 4086 13 = 9 ∧ acceleratedOrbit 13 4086 = 9827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4086 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4086) = 3 ^ 9 * m + 9827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4086.1, data_13_4086.2]

/-- Complete interval computation for depth 13, residue 4087. -/
theorem bounds_13_4087 : exactInterval 13 4087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4087 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4087) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4087 : oddCount 4087 13 = 9 ∧ acceleratedOrbit 13 4087 = 9827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4087 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4087) = 3 ^ 9 * m + 9827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4087.1, data_13_4087.2]

/-- Complete interval computation for depth 13, residue 4088. -/
theorem bounds_13_4088 : exactInterval 13 4088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4088 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4088) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4088 : oddCount 4088 13 = 9 ∧ acceleratedOrbit 13 4088 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4088 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4088) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4088.1, data_13_4088.2]

/-- Complete interval computation for depth 13, residue 4089. -/
theorem bounds_13_4089 : exactInterval 13 4089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4089 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4089) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4089 : oddCount 4089 13 = 8 ∧ acceleratedOrbit 13 4089 = 3277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4089 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4089) = 3 ^ 8 * m + 3277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4089.1, data_13_4089.2]

end Collatz.Research.StoppingAtlas.Batch0733
