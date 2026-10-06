import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0467

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 4085. -/
theorem bounds_12_4085 : exactInterval 12 4085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4085 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4085) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4085 : oddCount 4085 12 = 8 ∧ acceleratedOrbit 12 4085 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4085 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4085) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4085.1, data_12_4085.2]

/-- Complete interval computation for depth 12, residue 4086. -/
theorem bounds_12_4086 : exactInterval 12 4086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4086 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4086) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4086 : oddCount 4086 12 = 8 ∧ acceleratedOrbit 12 4086 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4086 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4086) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4086.1, data_12_4086.2]

/-- Complete interval computation for depth 12, residue 4087. -/
theorem bounds_12_4087 : exactInterval 12 4087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4087 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4087) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4087 : oddCount 4087 12 = 8 ∧ acceleratedOrbit 12 4087 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4087 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4087) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4087.1, data_12_4087.2]

/-- Complete interval computation for depth 12, residue 4088. -/
theorem bounds_12_4088 : exactInterval 12 4088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4088 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4088) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4088 : oddCount 4088 12 = 9 ∧ acceleratedOrbit 12 4088 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4088 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4088) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4088.1, data_12_4088.2]

/-- Complete interval computation for depth 12, residue 4089. -/
theorem bounds_12_4089 : exactInterval 12 4089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4089 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4089) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4089 : oddCount 4089 12 = 8 ∧ acceleratedOrbit 12 4089 = 6554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4089 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4089) = 3 ^ 8 * m + 6554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4089.1, data_12_4089.2]

/-- Complete interval computation for depth 12, residue 4090. -/
theorem bounds_12_4090 : exactInterval 12 4090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4090 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4090) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4090 : oddCount 4090 12 = 9 ∧ acceleratedOrbit 12 4090 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4090 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4090) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4090.1, data_12_4090.2]

/-- Complete interval computation for depth 12, residue 4091. -/
theorem bounds_12_4091 : exactInterval 12 4091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4091 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4091) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4091 : oddCount 4091 12 = 8 ∧ acceleratedOrbit 12 4091 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4091 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4091) = 3 ^ 8 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4091.1, data_12_4091.2]

/-- Complete interval computation for depth 12, residue 4092. -/
theorem bounds_12_4092 : exactInterval 12 4092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4092 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4092) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4092 : oddCount 4092 12 = 10 ∧ acceleratedOrbit 12 4092 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4092 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4092) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4092.1, data_12_4092.2]

/-- Complete interval computation for depth 12, residue 4093. -/
theorem bounds_12_4093 : exactInterval 12 4093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4093 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4093) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4093 : oddCount 4093 12 = 10 ∧ acceleratedOrbit 12 4093 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4093 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4093) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4093.1, data_12_4093.2]

/-- Complete interval computation for depth 12, residue 4094. -/
theorem bounds_12_4094 : exactInterval 12 4094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4094 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4094) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4094 : oddCount 4094 12 = 11 ∧ acceleratedOrbit 12 4094 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4094 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4094) = 3 ^ 11 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4094.1, data_12_4094.2]

/-- Complete interval computation for depth 12, residue 4095. -/
theorem bounds_12_4095 : exactInterval 12 4095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_4095 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 4095) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_4095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_4095 : oddCount 4095 12 = 12 ∧ acceleratedOrbit 12 4095 = 531440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_4095 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 4095) = 3 ^ 12 * m + 531440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_4095.1, data_12_4095.2]

/-- Complete interval computation for depth 13, residue 0. -/
theorem bounds_13_0 : exactInterval 13 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_0 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 0) 13 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_0 : oddCount 0 13 = 0 ∧ acceleratedOrbit 13 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_0 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_0.1, data_13_0.2]

/-- Complete interval computation for depth 13, residue 1. -/
theorem bounds_13_1 : exactInterval 13 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1) 13 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1 : oddCount 1 13 = 7 ∧ acceleratedOrbit 13 1 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1) = 3 ^ 7 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1.1, data_13_1.2]

/-- Complete interval computation for depth 13, residue 2. -/
theorem bounds_13_2 : exactInterval 13 2 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2 : oddCount 2 13 = 6 ∧ acceleratedOrbit 13 2 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2.1, data_13_2.2]

/-- Complete interval computation for depth 13, residue 3. -/
theorem bounds_13_3 : exactInterval 13 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3 : oddCount 3 13 = 6 ∧ acceleratedOrbit 13 3 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3) = 3 ^ 6 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3.1, data_13_3.2]

/-- Complete interval computation for depth 13, residue 4. -/
theorem bounds_13_4 : exactInterval 13 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4 : oddCount 4 13 = 6 ∧ acceleratedOrbit 13 4 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4.1, data_13_4.2]

end Collatz.Research.StoppingAtlas.Batch0467
