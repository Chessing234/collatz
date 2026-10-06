import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0750

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4336. -/
theorem bounds_13_4336 : exactInterval 13 4336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4336 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4336) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4336 : oddCount 4336 13 = 4 ∧ acceleratedOrbit 13 4336 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4336 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4336) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4336.1, data_13_4336.2]

/-- Complete interval computation for depth 13, residue 4337. -/
theorem bounds_13_4337 : exactInterval 13 4337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4337 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4337) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4337 : oddCount 4337 13 = 4 ∧ acceleratedOrbit 13 4337 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4337 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4337) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4337.1, data_13_4337.2]

/-- Complete interval computation for depth 13, residue 4338. -/
theorem bounds_13_4338 : exactInterval 13 4338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4338 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4338) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4338 : oddCount 4338 13 = 8 ∧ acceleratedOrbit 13 4338 = 3478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4338 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4338) = 3 ^ 8 * m + 3478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4338.1, data_13_4338.2]

/-- Complete interval computation for depth 13, residue 4339. -/
theorem bounds_13_4339 : exactInterval 13 4339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4339 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4339) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4339 : oddCount 4339 13 = 8 ∧ acceleratedOrbit 13 4339 = 3478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4339 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4339) = 3 ^ 8 * m + 3478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4339.1, data_13_4339.2]

/-- Complete interval computation for depth 13, residue 4340. -/
theorem bounds_13_4340 : exactInterval 13 4340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4340 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4340) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4340 : oddCount 4340 13 = 4 ∧ acceleratedOrbit 13 4340 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4340 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4340) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4340.1, data_13_4340.2]

/-- Complete interval computation for depth 13, residue 4341. -/
theorem bounds_13_4341 : exactInterval 13 4341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4341 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4341) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4341 : oddCount 4341 13 = 4 ∧ acceleratedOrbit 13 4341 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4341 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4341) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4341.1, data_13_4341.2]

/-- Complete interval computation for depth 13, residue 4342. -/
theorem bounds_13_4342 : exactInterval 13 4342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4342 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4342) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4342 : oddCount 4342 13 = 8 ∧ acceleratedOrbit 13 4342 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4342 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4342) = 3 ^ 8 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4342.1, data_13_4342.2]

/-- Complete interval computation for depth 13, residue 4343. -/
theorem bounds_13_4343 : exactInterval 13 4343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4343 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4343) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4343 : oddCount 4343 13 = 8 ∧ acceleratedOrbit 13 4343 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4343 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4343) = 3 ^ 8 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4343.1, data_13_4343.2]

/-- Complete interval computation for depth 13, residue 4344. -/
theorem bounds_13_4344 : exactInterval 13 4344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4344 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4344) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4344 : oddCount 4344 13 = 7 ∧ acceleratedOrbit 13 4344 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4344 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4344) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4344.1, data_13_4344.2]

/-- Complete interval computation for depth 13, residue 4345. -/
theorem bounds_13_4345 : exactInterval 13 4345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4345 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4345) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4345 : oddCount 4345 13 = 9 ∧ acceleratedOrbit 13 4345 = 10448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4345 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4345) = 3 ^ 9 * m + 10448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4345.1, data_13_4345.2]

/-- Complete interval computation for depth 13, residue 4346. -/
theorem bounds_13_4346 : exactInterval 13 4346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4346 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4346) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4346 : oddCount 4346 13 = 7 ∧ acceleratedOrbit 13 4346 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4346 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4346) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4346.1, data_13_4346.2]

/-- Complete interval computation for depth 13, residue 4347. -/
theorem bounds_13_4347 : exactInterval 13 4347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4347 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4347) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4347 : oddCount 4347 13 = 11 ∧ acceleratedOrbit 13 4347 = 94040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4347 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4347) = 3 ^ 11 * m + 94040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4347.1, data_13_4347.2]

/-- Complete interval computation for depth 13, residue 4348. -/
theorem bounds_13_4348 : exactInterval 13 4348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4348 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4348) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4348 : oddCount 4348 13 = 7 ∧ acceleratedOrbit 13 4348 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4348 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4348) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4348.1, data_13_4348.2]

/-- Complete interval computation for depth 13, residue 4349. -/
theorem bounds_13_4349 : exactInterval 13 4349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4349 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4349) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4349 : oddCount 4349 13 = 7 ∧ acceleratedOrbit 13 4349 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4349 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4349) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4349.1, data_13_4349.2]

/-- Complete interval computation for depth 13, residue 4350. -/
theorem bounds_13_4350 : exactInterval 13 4350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4350 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4350) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4350 : oddCount 4350 13 = 9 ∧ acceleratedOrbit 13 4350 = 10457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4350 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4350) = 3 ^ 9 * m + 10457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4350.1, data_13_4350.2]

/-- Complete interval computation for depth 13, residue 4351. -/
theorem bounds_13_4351 : exactInterval 13 4351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4351 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4351) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4351 : oddCount 4351 13 = 9 ∧ acceleratedOrbit 13 4351 = 10457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4351 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4351) = 3 ^ 9 * m + 10457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4351.1, data_13_4351.2]

end Collatz.Research.StoppingAtlas.Batch0750
