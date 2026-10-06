import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0958

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31358. -/
theorem bounds_15_31358 : exactInterval 15 31358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31358 : oddCount 31358 15 = 10 ∧ acceleratedOrbit 15 31358 = 56513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31358) = 3 ^ 10 * m + 56513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31358.1, data_15_31358.2]

/-- Complete interval computation for depth 15, residue 31359. -/
theorem bounds_15_31359 : exactInterval 15 31359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31359 : oddCount 31359 15 = 10 ∧ acceleratedOrbit 15 31359 = 56512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31359) = 3 ^ 10 * m + 56512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31359.1, data_15_31359.2]

/-- Complete interval computation for depth 15, residue 31360. -/
theorem bounds_15_31360 : exactInterval 15 31360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31360 : oddCount 31360 15 = 4 ∧ acceleratedOrbit 15 31360 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31360) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31360.1, data_15_31360.2]

/-- Complete interval computation for depth 15, residue 31361. -/
theorem bounds_15_31361 : exactInterval 15 31361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31361 : oddCount 31361 15 = 8 ∧ acceleratedOrbit 15 31361 = 6280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31361) = 3 ^ 8 * m + 6280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31361.1, data_15_31361.2]

/-- Complete interval computation for depth 15, residue 31362. -/
theorem bounds_15_31362 : exactInterval 15 31362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31362 : oddCount 31362 15 = 7 ∧ acceleratedOrbit 15 31362 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31362) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31362.1, data_15_31362.2]

/-- Complete interval computation for depth 15, residue 31363. -/
theorem bounds_15_31363 : exactInterval 15 31363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31363 : oddCount 31363 15 = 7 ∧ acceleratedOrbit 15 31363 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31363) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31363.1, data_15_31363.2]

/-- Complete interval computation for depth 15, residue 31364. -/
theorem bounds_15_31364 : exactInterval 15 31364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31364 : oddCount 31364 15 = 6 ∧ acceleratedOrbit 15 31364 = 698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31364) = 3 ^ 6 * m + 698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31364.1, data_15_31364.2]

/-- Complete interval computation for depth 15, residue 31365. -/
theorem bounds_15_31365 : exactInterval 15 31365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31365 : oddCount 31365 15 = 6 ∧ acceleratedOrbit 15 31365 = 698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31365) = 3 ^ 6 * m + 698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31365.1, data_15_31365.2]

/-- Complete interval computation for depth 15, residue 31366. -/
theorem bounds_15_31366 : exactInterval 15 31366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31366 : oddCount 31366 15 = 6 ∧ acceleratedOrbit 15 31366 = 698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31366) = 3 ^ 6 * m + 698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31366.1, data_15_31366.2]

/-- Complete interval computation for depth 15, residue 31367. -/
theorem bounds_15_31367 : exactInterval 15 31367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31367 : oddCount 31367 15 = 6 ∧ acceleratedOrbit 15 31367 = 698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31367) = 3 ^ 6 * m + 698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31367.1, data_15_31367.2]

/-- Complete interval computation for depth 15, residue 31368. -/
theorem bounds_15_31368 : exactInterval 15 31368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31368 : oddCount 31368 15 = 7 ∧ acceleratedOrbit 15 31368 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31368) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31368.1, data_15_31368.2]

/-- Complete interval computation for depth 15, residue 31369. -/
theorem bounds_15_31369 : exactInterval 15 31369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31369 : oddCount 31369 15 = 9 ∧ acceleratedOrbit 15 31369 = 18845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31369) = 3 ^ 9 * m + 18845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31369.1, data_15_31369.2]

/-- Complete interval computation for depth 15, residue 31370. -/
theorem bounds_15_31370 : exactInterval 15 31370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31370 : oddCount 31370 15 = 7 ∧ acceleratedOrbit 15 31370 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31370) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31370.1, data_15_31370.2]

/-- Complete interval computation for depth 15, residue 31371. -/
theorem bounds_15_31371 : exactInterval 15 31371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31371 : oddCount 31371 15 = 6 ∧ acceleratedOrbit 15 31371 = 698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31371) = 3 ^ 6 * m + 698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31371.1, data_15_31371.2]

/-- Complete interval computation for depth 15, residue 31372. -/
theorem bounds_15_31372 : exactInterval 15 31372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31372 : oddCount 31372 15 = 7 ∧ acceleratedOrbit 15 31372 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31372) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31372.1, data_15_31372.2]

/-- Complete interval computation for depth 15, residue 31373. -/
theorem bounds_15_31373 : exactInterval 15 31373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31373 : oddCount 31373 15 = 7 ∧ acceleratedOrbit 15 31373 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31373) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31373.1, data_15_31373.2]

/-- Complete interval computation for depth 15, residue 31374. -/
theorem bounds_15_31374 : exactInterval 15 31374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31374 : oddCount 31374 15 = 9 ∧ acceleratedOrbit 15 31374 = 18848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31374) = 3 ^ 9 * m + 18848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31374.1, data_15_31374.2]

/-- Complete interval computation for depth 15, residue 31375. -/
theorem bounds_15_31375 : exactInterval 15 31375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31375 : oddCount 31375 15 = 9 ∧ acceleratedOrbit 15 31375 = 18848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31375) = 3 ^ 9 * m + 18848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31375.1, data_15_31375.2]

/-- Complete interval computation for depth 15, residue 31376. -/
theorem bounds_15_31376 : exactInterval 15 31376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31376 : oddCount 31376 15 = 9 ∧ acceleratedOrbit 15 31376 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31376) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31376.1, data_15_31376.2]

/-- Complete interval computation for depth 15, residue 31377. -/
theorem bounds_15_31377 : exactInterval 15 31377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31377 : oddCount 31377 15 = 8 ∧ acceleratedOrbit 15 31377 = 6284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31377) = 3 ^ 8 * m + 6284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31377.1, data_15_31377.2]

/-- Complete interval computation for depth 15, residue 31378. -/
theorem bounds_15_31378 : exactInterval 15 31378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31378 : oddCount 31378 15 = 8 ∧ acceleratedOrbit 15 31378 = 6284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31378) = 3 ^ 8 * m + 6284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31378.1, data_15_31378.2]

/-- Complete interval computation for depth 15, residue 31379. -/
theorem bounds_15_31379 : exactInterval 15 31379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31379 : oddCount 31379 15 = 8 ∧ acceleratedOrbit 15 31379 = 6284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31379) = 3 ^ 8 * m + 6284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31379.1, data_15_31379.2]

/-- Complete interval computation for depth 15, residue 31380. -/
theorem bounds_15_31380 : exactInterval 15 31380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31380 : oddCount 31380 15 = 9 ∧ acceleratedOrbit 15 31380 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31380) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31380.1, data_15_31380.2]

/-- Complete interval computation for depth 15, residue 31381. -/
theorem bounds_15_31381 : exactInterval 15 31381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31381 : oddCount 31381 15 = 9 ∧ acceleratedOrbit 15 31381 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31381) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31381.1, data_15_31381.2]

/-- Complete interval computation for depth 15, residue 31382. -/
theorem bounds_15_31382 : exactInterval 15 31382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31382 : oddCount 31382 15 = 7 ∧ acceleratedOrbit 15 31382 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31382) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31382.1, data_15_31382.2]

/-- Complete interval computation for depth 15, residue 31383. -/
theorem bounds_15_31383 : exactInterval 15 31383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31383 : oddCount 31383 15 = 7 ∧ acceleratedOrbit 15 31383 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31383) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31383.1, data_15_31383.2]

/-- Complete interval computation for depth 15, residue 31384. -/
theorem bounds_15_31384 : exactInterval 15 31384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31384 : oddCount 31384 15 = 9 ∧ acceleratedOrbit 15 31384 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31384) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31384.1, data_15_31384.2]

/-- Complete interval computation for depth 15, residue 31385. -/
theorem bounds_15_31385 : exactInterval 15 31385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31385 : oddCount 31385 15 = 7 ∧ acceleratedOrbit 15 31385 = 2095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31385) = 3 ^ 7 * m + 2095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31385.1, data_15_31385.2]

/-- Complete interval computation for depth 15, residue 31386. -/
theorem bounds_15_31386 : exactInterval 15 31386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31386 : oddCount 31386 15 = 9 ∧ acceleratedOrbit 15 31386 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31386) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31386.1, data_15_31386.2]

/-- Complete interval computation for depth 15, residue 31387. -/
theorem bounds_15_31387 : exactInterval 15 31387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31387 : oddCount 31387 15 = 11 ∧ acceleratedOrbit 15 31387 = 169690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31387) = 3 ^ 11 * m + 169690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31387.1, data_15_31387.2]

/-- Complete interval computation for depth 15, residue 31388. -/
theorem bounds_15_31388 : exactInterval 15 31388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31388 : oddCount 31388 15 = 8 ∧ acceleratedOrbit 15 31388 = 6286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31388) = 3 ^ 8 * m + 6286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31388.1, data_15_31388.2]

/-- Complete interval computation for depth 15, residue 31389. -/
theorem bounds_15_31389 : exactInterval 15 31389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31389 : oddCount 31389 15 = 8 ∧ acceleratedOrbit 15 31389 = 6286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31389) = 3 ^ 8 * m + 6286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31389.1, data_15_31389.2]

/-- Complete interval computation for depth 15, residue 31390. -/
theorem bounds_15_31390 : exactInterval 15 31390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31390 : oddCount 31390 15 = 8 ∧ acceleratedOrbit 15 31390 = 6286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31390) = 3 ^ 8 * m + 6286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31390.1, data_15_31390.2]

end Collatz.Research.PassageAtlas.Batch0958
