import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0134

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4358. -/
theorem bounds_15_4358 : exactInterval 15 4358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4358 : oddCount 4358 15 = 6 ∧ acceleratedOrbit 15 4358 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4358) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4358.1, data_15_4358.2]

/-- Complete interval computation for depth 15, residue 4359. -/
theorem bounds_15_4359 : exactInterval 15 4359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4359 : oddCount 4359 15 = 9 ∧ acceleratedOrbit 15 4359 = 2620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4359) = 3 ^ 9 * m + 2620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4359.1, data_15_4359.2]

/-- Complete interval computation for depth 15, residue 4360. -/
theorem bounds_15_4360 : exactInterval 15 4360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4360 : oddCount 4360 15 = 6 ∧ acceleratedOrbit 15 4360 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4360) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4360.1, data_15_4360.2]

/-- Complete interval computation for depth 15, residue 4361. -/
theorem bounds_15_4361 : exactInterval 15 4361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4361 : oddCount 4361 15 = 8 ∧ acceleratedOrbit 15 4361 = 874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4361) = 3 ^ 8 * m + 874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4361.1, data_15_4361.2]

/-- Complete interval computation for depth 15, residue 4362. -/
theorem bounds_15_4362 : exactInterval 15 4362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4362 : oddCount 4362 15 = 6 ∧ acceleratedOrbit 15 4362 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4362) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4362.1, data_15_4362.2]

/-- Complete interval computation for depth 15, residue 4363. -/
theorem bounds_15_4363 : exactInterval 15 4363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4363 : oddCount 4363 15 = 7 ∧ acceleratedOrbit 15 4363 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4363) = 3 ^ 7 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4363.1, data_15_4363.2]

/-- Complete interval computation for depth 15, residue 4364. -/
theorem bounds_15_4364 : exactInterval 15 4364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4364 : oddCount 4364 15 = 6 ∧ acceleratedOrbit 15 4364 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4364) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4364.1, data_15_4364.2]

/-- Complete interval computation for depth 15, residue 4365. -/
theorem bounds_15_4365 : exactInterval 15 4365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4365 : oddCount 4365 15 = 6 ∧ acceleratedOrbit 15 4365 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4365) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4365.1, data_15_4365.2]

/-- Complete interval computation for depth 15, residue 4366. -/
theorem bounds_15_4366 : exactInterval 15 4366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4366 : oddCount 4366 15 = 7 ∧ acceleratedOrbit 15 4366 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4366) = 3 ^ 7 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4366.1, data_15_4366.2]

/-- Complete interval computation for depth 15, residue 4367. -/
theorem bounds_15_4367 : exactInterval 15 4367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4367 : oddCount 4367 15 = 7 ∧ acceleratedOrbit 15 4367 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4367) = 3 ^ 7 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4367.1, data_15_4367.2]

/-- Complete interval computation for depth 15, residue 4368. -/
theorem bounds_15_4368 : exactInterval 15 4368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4368 : oddCount 4368 15 = 4 ∧ acceleratedOrbit 15 4368 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4368) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4368.1, data_15_4368.2]

/-- Complete interval computation for depth 15, residue 4369. -/
theorem bounds_15_4369 : exactInterval 15 4369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4369 : oddCount 4369 15 = 6 ∧ acceleratedOrbit 15 4369 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4369) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4369.1, data_15_4369.2]

/-- Complete interval computation for depth 15, residue 4370. -/
theorem bounds_15_4370 : exactInterval 15 4370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4370 : oddCount 4370 15 = 10 ∧ acceleratedOrbit 15 4370 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4370) = 3 ^ 10 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4370.1, data_15_4370.2]

/-- Complete interval computation for depth 15, residue 4371. -/
theorem bounds_15_4371 : exactInterval 15 4371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4371 : oddCount 4371 15 = 10 ∧ acceleratedOrbit 15 4371 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4371) = 3 ^ 10 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4371.1, data_15_4371.2]

/-- Complete interval computation for depth 15, residue 4372. -/
theorem bounds_15_4372 : exactInterval 15 4372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4372 : oddCount 4372 15 = 4 ∧ acceleratedOrbit 15 4372 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4372) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4372.1, data_15_4372.2]

/-- Complete interval computation for depth 15, residue 4373. -/
theorem bounds_15_4373 : exactInterval 15 4373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4373 : oddCount 4373 15 = 4 ∧ acceleratedOrbit 15 4373 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4373) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4373.1, data_15_4373.2]

/-- Complete interval computation for depth 15, residue 4374. -/
theorem bounds_15_4374 : exactInterval 15 4374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4374 : oddCount 4374 15 = 9 ∧ acceleratedOrbit 15 4374 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4374) = 3 ^ 9 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4374.1, data_15_4374.2]

/-- Complete interval computation for depth 15, residue 4375. -/
theorem bounds_15_4375 : exactInterval 15 4375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4375 : oddCount 4375 15 = 9 ∧ acceleratedOrbit 15 4375 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4375) = 3 ^ 9 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4375.1, data_15_4375.2]

/-- Complete interval computation for depth 15, residue 4376. -/
theorem bounds_15_4376 : exactInterval 15 4376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4376 : oddCount 4376 15 = 4 ∧ acceleratedOrbit 15 4376 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4376) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4376.1, data_15_4376.2]

/-- Complete interval computation for depth 15, residue 4377. -/
theorem bounds_15_4377 : exactInterval 15 4377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4377 : oddCount 4377 15 = 9 ∧ acceleratedOrbit 15 4377 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4377) = 3 ^ 9 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4377.1, data_15_4377.2]

/-- Complete interval computation for depth 15, residue 4378. -/
theorem bounds_15_4378 : exactInterval 15 4378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4378 : oddCount 4378 15 = 4 ∧ acceleratedOrbit 15 4378 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4378) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4378.1, data_15_4378.2]

/-- Complete interval computation for depth 15, residue 4379. -/
theorem bounds_15_4379 : exactInterval 15 4379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4379 : oddCount 4379 15 = 10 ∧ acceleratedOrbit 15 4379 = 7894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4379) = 3 ^ 10 * m + 7894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4379.1, data_15_4379.2]

/-- Complete interval computation for depth 15, residue 4380. -/
theorem bounds_15_4380 : exactInterval 15 4380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4380 : oddCount 4380 15 = 9 ∧ acceleratedOrbit 15 4380 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4380) = 3 ^ 9 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4380.1, data_15_4380.2]

/-- Complete interval computation for depth 15, residue 4381. -/
theorem bounds_15_4381 : exactInterval 15 4381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4381 : oddCount 4381 15 = 9 ∧ acceleratedOrbit 15 4381 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4381) = 3 ^ 9 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4381.1, data_15_4381.2]

/-- Complete interval computation for depth 15, residue 4382. -/
theorem bounds_15_4382 : exactInterval 15 4382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4382 : oddCount 4382 15 = 9 ∧ acceleratedOrbit 15 4382 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4382) = 3 ^ 9 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4382.1, data_15_4382.2]

/-- Complete interval computation for depth 15, residue 4383. -/
theorem bounds_15_4383 : exactInterval 15 4383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4383 : oddCount 4383 15 = 8 ∧ acceleratedOrbit 15 4383 = 878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4383) = 3 ^ 8 * m + 878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4383.1, data_15_4383.2]

/-- Complete interval computation for depth 15, residue 4384. -/
theorem bounds_15_4384 : exactInterval 15 4384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4384 : oddCount 4384 15 = 8 ∧ acceleratedOrbit 15 4384 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4384) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4384.1, data_15_4384.2]

/-- Complete interval computation for depth 15, residue 4385. -/
theorem bounds_15_4385 : exactInterval 15 4385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4385 : oddCount 4385 15 = 8 ∧ acceleratedOrbit 15 4385 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4385) = 3 ^ 8 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4385.1, data_15_4385.2]

/-- Complete interval computation for depth 15, residue 4386. -/
theorem bounds_15_4386 : exactInterval 15 4386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4386 : oddCount 4386 15 = 8 ∧ acceleratedOrbit 15 4386 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4386) = 3 ^ 8 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4386.1, data_15_4386.2]

/-- Complete interval computation for depth 15, residue 4387. -/
theorem bounds_15_4387 : exactInterval 15 4387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4387 : oddCount 4387 15 = 8 ∧ acceleratedOrbit 15 4387 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4387) = 3 ^ 8 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4387.1, data_15_4387.2]

/-- Complete interval computation for depth 15, residue 4388. -/
theorem bounds_15_4388 : exactInterval 15 4388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4388 : oddCount 4388 15 = 8 ∧ acceleratedOrbit 15 4388 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4388) = 3 ^ 8 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4388.1, data_15_4388.2]

/-- Complete interval computation for depth 15, residue 4389. -/
theorem bounds_15_4389 : exactInterval 15 4389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4389 : oddCount 4389 15 = 8 ∧ acceleratedOrbit 15 4389 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4389) = 3 ^ 8 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4389.1, data_15_4389.2]

end Collatz.Research.PassageAtlas.Batch0134
