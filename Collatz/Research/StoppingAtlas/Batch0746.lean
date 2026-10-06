import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0746

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4275. -/
theorem bounds_13_4275 : exactInterval 13 4275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4275 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4275) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4275 : oddCount 4275 13 = 5 ∧ acceleratedOrbit 13 4275 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4275 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4275) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4275.1, data_13_4275.2]

/-- Complete interval computation for depth 13, residue 4276. -/
theorem bounds_13_4276 : exactInterval 13 4276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4276 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4276) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4276 : oddCount 4276 13 = 5 ∧ acceleratedOrbit 13 4276 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4276 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4276) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4276.1, data_13_4276.2]

/-- Complete interval computation for depth 13, residue 4277. -/
theorem bounds_13_4277 : exactInterval 13 4277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4277 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4277) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4277 : oddCount 4277 13 = 5 ∧ acceleratedOrbit 13 4277 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4277 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4277) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4277.1, data_13_4277.2]

/-- Complete interval computation for depth 13, residue 4278. -/
theorem bounds_13_4278 : exactInterval 13 4278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4278 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4278) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4278 : oddCount 4278 13 = 10 ∧ acceleratedOrbit 13 4278 = 30860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4278 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4278) = 3 ^ 10 * m + 30860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4278.1, data_13_4278.2]

/-- Complete interval computation for depth 13, residue 4279. -/
theorem bounds_13_4279 : exactInterval 13 4279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4279 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4279) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4279 : oddCount 4279 13 = 10 ∧ acceleratedOrbit 13 4279 = 30860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4279 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4279) = 3 ^ 10 * m + 30860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4279.1, data_13_4279.2]

/-- Complete interval computation for depth 13, residue 4280. -/
theorem bounds_13_4280 : exactInterval 13 4280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4280 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4280) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4280 : oddCount 4280 13 = 5 ∧ acceleratedOrbit 13 4280 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4280 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4280) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4280.1, data_13_4280.2]

/-- Complete interval computation for depth 13, residue 4281. -/
theorem bounds_13_4281 : exactInterval 13 4281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4281 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4281) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4281 : oddCount 4281 13 = 7 ∧ acceleratedOrbit 13 4281 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4281 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4281) = 3 ^ 7 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4281.1, data_13_4281.2]

/-- Complete interval computation for depth 13, residue 4282. -/
theorem bounds_13_4282 : exactInterval 13 4282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4282 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4282) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4282 : oddCount 4282 13 = 5 ∧ acceleratedOrbit 13 4282 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4282 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4282) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4282.1, data_13_4282.2]

/-- Complete interval computation for depth 13, residue 4283. -/
theorem bounds_13_4283 : exactInterval 13 4283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4283 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4283) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4283 : oddCount 4283 13 = 7 ∧ acceleratedOrbit 13 4283 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4283 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4283) = 3 ^ 7 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4283.1, data_13_4283.2]

/-- Complete interval computation for depth 13, residue 4284. -/
theorem bounds_13_4284 : exactInterval 13 4284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4284 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4284) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4284 : oddCount 4284 13 = 7 ∧ acceleratedOrbit 13 4284 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4284 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4284) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4284.1, data_13_4284.2]

/-- Complete interval computation for depth 13, residue 4285. -/
theorem bounds_13_4285 : exactInterval 13 4285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4285 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4285) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4285 : oddCount 4285 13 = 7 ∧ acceleratedOrbit 13 4285 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4285 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4285) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4285.1, data_13_4285.2]

/-- Complete interval computation for depth 13, residue 4286. -/
theorem bounds_13_4286 : exactInterval 13 4286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4286 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4286) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4286 : oddCount 4286 13 = 7 ∧ acceleratedOrbit 13 4286 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4286 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4286) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4286.1, data_13_4286.2]

/-- Complete interval computation for depth 13, residue 4287. -/
theorem bounds_13_4287 : exactInterval 13 4287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4287 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4287) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4287 : oddCount 4287 13 = 9 ∧ acceleratedOrbit 13 4287 = 10304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4287 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4287) = 3 ^ 9 * m + 10304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4287.1, data_13_4287.2]

/-- Complete interval computation for depth 13, residue 4288. -/
theorem bounds_13_4288 : exactInterval 13 4288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4288 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4288) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4288 : oddCount 4288 13 = 4 ∧ acceleratedOrbit 13 4288 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4288 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4288) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4288.1, data_13_4288.2]

/-- Complete interval computation for depth 13, residue 4289. -/
theorem bounds_13_4289 : exactInterval 13 4289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4289 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4289) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4289 : oddCount 4289 13 = 7 ∧ acceleratedOrbit 13 4289 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4289 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4289) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4289.1, data_13_4289.2]

end Collatz.Research.StoppingAtlas.Batch0746
