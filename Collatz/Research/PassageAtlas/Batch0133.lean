import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0133

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4325. -/
theorem bounds_15_4325 : exactInterval 15 4325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4325 : oddCount 4325 15 = 7 ∧ acceleratedOrbit 15 4325 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4325) = 3 ^ 7 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4325.1, data_15_4325.2]

/-- Complete interval computation for depth 15, residue 4326. -/
theorem bounds_15_4326 : exactInterval 15 4326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4326 : oddCount 4326 15 = 7 ∧ acceleratedOrbit 15 4326 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4326) = 3 ^ 7 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4326.1, data_15_4326.2]

/-- Complete interval computation for depth 15, residue 4327. -/
theorem bounds_15_4327 : exactInterval 15 4327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4327 : oddCount 4327 15 = 10 ∧ acceleratedOrbit 15 4327 = 7802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4327) = 3 ^ 10 * m + 7802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4327.1, data_15_4327.2]

/-- Complete interval computation for depth 15, residue 4328. -/
theorem bounds_15_4328 : exactInterval 15 4328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4328 : oddCount 4328 15 = 6 ∧ acceleratedOrbit 15 4328 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4328) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4328.1, data_15_4328.2]

/-- Complete interval computation for depth 15, residue 4329. -/
theorem bounds_15_4329 : exactInterval 15 4329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4329 : oddCount 4329 15 = 9 ∧ acceleratedOrbit 15 4329 = 2602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4329) = 3 ^ 9 * m + 2602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4329.1, data_15_4329.2]

/-- Complete interval computation for depth 15, residue 4330. -/
theorem bounds_15_4330 : exactInterval 15 4330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4330 : oddCount 4330 15 = 6 ∧ acceleratedOrbit 15 4330 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4330) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4330.1, data_15_4330.2]

/-- Complete interval computation for depth 15, residue 4331. -/
theorem bounds_15_4331 : exactInterval 15 4331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4331 : oddCount 4331 15 = 9 ∧ acceleratedOrbit 15 4331 = 2603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4331) = 3 ^ 9 * m + 2603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4331.1, data_15_4331.2]

/-- Complete interval computation for depth 15, residue 4332. -/
theorem bounds_15_4332 : exactInterval 15 4332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4332 : oddCount 4332 15 = 7 ∧ acceleratedOrbit 15 4332 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4332) = 3 ^ 7 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4332.1, data_15_4332.2]

/-- Complete interval computation for depth 15, residue 4333. -/
theorem bounds_15_4333 : exactInterval 15 4333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4333 : oddCount 4333 15 = 7 ∧ acceleratedOrbit 15 4333 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4333) = 3 ^ 7 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4333.1, data_15_4333.2]

/-- Complete interval computation for depth 15, residue 4334. -/
theorem bounds_15_4334 : exactInterval 15 4334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4334 : oddCount 4334 15 = 7 ∧ acceleratedOrbit 15 4334 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4334) = 3 ^ 7 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4334.1, data_15_4334.2]

/-- Complete interval computation for depth 15, residue 4335. -/
theorem bounds_15_4335 : exactInterval 15 4335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4335 : oddCount 4335 15 = 10 ∧ acceleratedOrbit 15 4335 = 7814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4335) = 3 ^ 10 * m + 7814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4335.1, data_15_4335.2]

/-- Complete interval computation for depth 15, residue 4336. -/
theorem bounds_15_4336 : exactInterval 15 4336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4336 : oddCount 4336 15 = 6 ∧ acceleratedOrbit 15 4336 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4336) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4336.1, data_15_4336.2]

/-- Complete interval computation for depth 15, residue 4337. -/
theorem bounds_15_4337 : exactInterval 15 4337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4337 : oddCount 4337 15 = 6 ∧ acceleratedOrbit 15 4337 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4337) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4337.1, data_15_4337.2]

/-- Complete interval computation for depth 15, residue 4338. -/
theorem bounds_15_4338 : exactInterval 15 4338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4338 : oddCount 4338 15 = 9 ∧ acceleratedOrbit 15 4338 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4338) = 3 ^ 9 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4338.1, data_15_4338.2]

/-- Complete interval computation for depth 15, residue 4339. -/
theorem bounds_15_4339 : exactInterval 15 4339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4339 : oddCount 4339 15 = 9 ∧ acceleratedOrbit 15 4339 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4339) = 3 ^ 9 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4339.1, data_15_4339.2]

/-- Complete interval computation for depth 15, residue 4340. -/
theorem bounds_15_4340 : exactInterval 15 4340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4340 : oddCount 4340 15 = 6 ∧ acceleratedOrbit 15 4340 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4340) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4340.1, data_15_4340.2]

/-- Complete interval computation for depth 15, residue 4341. -/
theorem bounds_15_4341 : exactInterval 15 4341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4341 : oddCount 4341 15 = 6 ∧ acceleratedOrbit 15 4341 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4341) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4341.1, data_15_4341.2]

/-- Complete interval computation for depth 15, residue 4342. -/
theorem bounds_15_4342 : exactInterval 15 4342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4342 : oddCount 4342 15 = 9 ∧ acceleratedOrbit 15 4342 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4342) = 3 ^ 9 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4342.1, data_15_4342.2]

/-- Complete interval computation for depth 15, residue 4343. -/
theorem bounds_15_4343 : exactInterval 15 4343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4343 : oddCount 4343 15 = 9 ∧ acceleratedOrbit 15 4343 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4343) = 3 ^ 9 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4343.1, data_15_4343.2]

/-- Complete interval computation for depth 15, residue 4344. -/
theorem bounds_15_4344 : exactInterval 15 4344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4344 : oddCount 4344 15 = 8 ∧ acceleratedOrbit 15 4344 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4344) = 3 ^ 8 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4344.1, data_15_4344.2]

/-- Complete interval computation for depth 15, residue 4345. -/
theorem bounds_15_4345 : exactInterval 15 4345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4345 : oddCount 4345 15 = 9 ∧ acceleratedOrbit 15 4345 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4345) = 3 ^ 9 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4345.1, data_15_4345.2]

/-- Complete interval computation for depth 15, residue 4346. -/
theorem bounds_15_4346 : exactInterval 15 4346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4346 : oddCount 4346 15 = 8 ∧ acceleratedOrbit 15 4346 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4346) = 3 ^ 8 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4346.1, data_15_4346.2]

/-- Complete interval computation for depth 15, residue 4347. -/
theorem bounds_15_4347 : exactInterval 15 4347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4347 : oddCount 4347 15 = 11 ∧ acceleratedOrbit 15 4347 = 23510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4347) = 3 ^ 11 * m + 23510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4347.1, data_15_4347.2]

/-- Complete interval computation for depth 15, residue 4348. -/
theorem bounds_15_4348 : exactInterval 15 4348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4348 : oddCount 4348 15 = 8 ∧ acceleratedOrbit 15 4348 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4348) = 3 ^ 8 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4348.1, data_15_4348.2]

/-- Complete interval computation for depth 15, residue 4349. -/
theorem bounds_15_4349 : exactInterval 15 4349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4349 : oddCount 4349 15 = 8 ∧ acceleratedOrbit 15 4349 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4349) = 3 ^ 8 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4349.1, data_15_4349.2]

/-- Complete interval computation for depth 15, residue 4350. -/
theorem bounds_15_4350 : exactInterval 15 4350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4350 : oddCount 4350 15 = 10 ∧ acceleratedOrbit 15 4350 = 7843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4350) = 3 ^ 10 * m + 7843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4350.1, data_15_4350.2]

/-- Complete interval computation for depth 15, residue 4351. -/
theorem bounds_15_4351 : exactInterval 15 4351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4351 : oddCount 4351 15 = 10 ∧ acceleratedOrbit 15 4351 = 7843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4351) = 3 ^ 10 * m + 7843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4351.1, data_15_4351.2]

/-- Complete interval computation for depth 15, residue 4352. -/
theorem bounds_15_4352 : exactInterval 15 4352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4352 : oddCount 4352 15 = 3 ∧ acceleratedOrbit 15 4352 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4352) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4352.1, data_15_4352.2]

/-- Complete interval computation for depth 15, residue 4353. -/
theorem bounds_15_4353 : exactInterval 15 4353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4353 : oddCount 4353 15 = 6 ∧ acceleratedOrbit 15 4353 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4353) = 3 ^ 6 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4353.1, data_15_4353.2]

/-- Complete interval computation for depth 15, residue 4354. -/
theorem bounds_15_4354 : exactInterval 15 4354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4354 : oddCount 4354 15 = 6 ∧ acceleratedOrbit 15 4354 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4354) = 3 ^ 6 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4354.1, data_15_4354.2]

/-- Complete interval computation for depth 15, residue 4355. -/
theorem bounds_15_4355 : exactInterval 15 4355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4355 : oddCount 4355 15 = 6 ∧ acceleratedOrbit 15 4355 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4355) = 3 ^ 6 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4355.1, data_15_4355.2]

/-- Complete interval computation for depth 15, residue 4356. -/
theorem bounds_15_4356 : exactInterval 15 4356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4356 : oddCount 4356 15 = 6 ∧ acceleratedOrbit 15 4356 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4356) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4356.1, data_15_4356.2]

/-- Complete interval computation for depth 15, residue 4357. -/
theorem bounds_15_4357 : exactInterval 15 4357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4357 : oddCount 4357 15 = 6 ∧ acceleratedOrbit 15 4357 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4357) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4357.1, data_15_4357.2]

end Collatz.Research.PassageAtlas.Batch0133
