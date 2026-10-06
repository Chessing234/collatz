import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0734

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4090. -/
theorem bounds_13_4090 : exactInterval 13 4090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4090 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4090) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4090 : oddCount 4090 13 = 9 ∧ acceleratedOrbit 13 4090 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4090 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4090) = 3 ^ 9 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4090.1, data_13_4090.2]

/-- Complete interval computation for depth 13, residue 4091. -/
theorem bounds_13_4091 : exactInterval 13 4091 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4091 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4091) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4091 : oddCount 4091 13 = 8 ∧ acceleratedOrbit 13 4091 = 3278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4091 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4091) = 3 ^ 8 * m + 3278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4091.1, data_13_4091.2]

/-- Complete interval computation for depth 13, residue 4092. -/
theorem bounds_13_4092 : exactInterval 13 4092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4092 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4092) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4092 : oddCount 4092 13 = 10 ∧ acceleratedOrbit 13 4092 = 29524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4092 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4092) = 3 ^ 10 * m + 29524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4092.1, data_13_4092.2]

/-- Complete interval computation for depth 13, residue 4093. -/
theorem bounds_13_4093 : exactInterval 13 4093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4093 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4093) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4093 : oddCount 4093 13 = 10 ∧ acceleratedOrbit 13 4093 = 29524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4093 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4093) = 3 ^ 10 * m + 29524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4093.1, data_13_4093.2]

/-- Complete interval computation for depth 13, residue 4094. -/
theorem bounds_13_4094 : exactInterval 13 4094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4094 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4094) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4094 : oddCount 4094 13 = 11 ∧ acceleratedOrbit 13 4094 = 88573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4094 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4094) = 3 ^ 11 * m + 88573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4094.1, data_13_4094.2]

/-- Complete interval computation for depth 13, residue 4095. -/
theorem bounds_13_4095 : exactInterval 13 4095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4095 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4095) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4095 : oddCount 4095 13 = 12 ∧ acceleratedOrbit 13 4095 = 265720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4095 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4095) = 3 ^ 12 * m + 265720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4095.1, data_13_4095.2]

/-- Complete interval computation for depth 13, residue 4096. -/
theorem bounds_13_4096 : exactInterval 13 4096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4096 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4096) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4096 : oddCount 4096 13 = 1 ∧ acceleratedOrbit 13 4096 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4096 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4096) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4096.1, data_13_4096.2]

/-- Complete interval computation for depth 13, residue 4097. -/
theorem bounds_13_4097 : exactInterval 13 4097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4097 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4097) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4097 : oddCount 4097 13 = 6 ∧ acceleratedOrbit 13 4097 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4097 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4097) = 3 ^ 6 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4097.1, data_13_4097.2]

/-- Complete interval computation for depth 13, residue 4098. -/
theorem bounds_13_4098 : exactInterval 13 4098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4098 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4098) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4098 : oddCount 4098 13 = 7 ∧ acceleratedOrbit 13 4098 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4098 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4098) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4098.1, data_13_4098.2]

/-- Complete interval computation for depth 13, residue 4099. -/
theorem bounds_13_4099 : exactInterval 13 4099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4099 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4099) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4099 : oddCount 4099 13 = 7 ∧ acceleratedOrbit 13 4099 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4099 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4099) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4099.1, data_13_4099.2]

/-- Complete interval computation for depth 13, residue 4100. -/
theorem bounds_13_4100 : exactInterval 13 4100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4100 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4100) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4100 : oddCount 4100 13 = 5 ∧ acceleratedOrbit 13 4100 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4100 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4100) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4100.1, data_13_4100.2]

/-- Complete interval computation for depth 13, residue 4101. -/
theorem bounds_13_4101 : exactInterval 13 4101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4101 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4101) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4101 : oddCount 4101 13 = 5 ∧ acceleratedOrbit 13 4101 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4101 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4101) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4101.1, data_13_4101.2]

/-- Complete interval computation for depth 13, residue 4102. -/
theorem bounds_13_4102 : exactInterval 13 4102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4102 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4102) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4102 : oddCount 4102 13 = 5 ∧ acceleratedOrbit 13 4102 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4102 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4102) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4102.1, data_13_4102.2]

/-- Complete interval computation for depth 13, residue 4103. -/
theorem bounds_13_4103 : exactInterval 13 4103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4103 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4103) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4103 : oddCount 4103 13 = 7 ∧ acceleratedOrbit 13 4103 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4103 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4103) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4103.1, data_13_4103.2]

/-- Complete interval computation for depth 13, residue 4104. -/
theorem bounds_13_4104 : exactInterval 13 4104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4104 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4104) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4104 : oddCount 4104 13 = 6 ∧ acceleratedOrbit 13 4104 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4104 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4104) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4104.1, data_13_4104.2]

/-- Complete interval computation for depth 13, residue 4105. -/
theorem bounds_13_4105 : exactInterval 13 4105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4105 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4105) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4105 : oddCount 4105 13 = 7 ∧ acceleratedOrbit 13 4105 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4105 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4105) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4105.1, data_13_4105.2]

end Collatz.Research.StoppingAtlas.Batch0734
