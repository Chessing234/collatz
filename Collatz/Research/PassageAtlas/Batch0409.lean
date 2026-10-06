import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0409

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13369. -/
theorem bounds_15_13369 : exactInterval 15 13369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13369 : oddCount 13369 15 = 7 ∧ acceleratedOrbit 15 13369 = 893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13369) = 3 ^ 7 * m + 893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13369.1, data_15_13369.2]

/-- Complete interval computation for depth 15, residue 13370. -/
theorem bounds_15_13370 : exactInterval 15 13370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13370 : oddCount 13370 15 = 6 ∧ acceleratedOrbit 15 13370 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13370) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13370.1, data_15_13370.2]

/-- Complete interval computation for depth 15, residue 13371. -/
theorem bounds_15_13371 : exactInterval 15 13371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13371 : oddCount 13371 15 = 8 ∧ acceleratedOrbit 15 13371 = 2678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13371) = 3 ^ 8 * m + 2678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13371.1, data_15_13371.2]

/-- Complete interval computation for depth 15, residue 13372. -/
theorem bounds_15_13372 : exactInterval 15 13372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13372 : oddCount 13372 15 = 6 ∧ acceleratedOrbit 15 13372 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13372) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13372.1, data_15_13372.2]

/-- Complete interval computation for depth 15, residue 13373. -/
theorem bounds_15_13373 : exactInterval 15 13373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13373 : oddCount 13373 15 = 6 ∧ acceleratedOrbit 15 13373 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13373) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13373.1, data_15_13373.2]

/-- Complete interval computation for depth 15, residue 13374. -/
theorem bounds_15_13374 : exactInterval 15 13374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13374 : oddCount 13374 15 = 9 ∧ acceleratedOrbit 15 13374 = 8036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13374) = 3 ^ 9 * m + 8036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13374.1, data_15_13374.2]

/-- Complete interval computation for depth 15, residue 13375. -/
theorem bounds_15_13375 : exactInterval 15 13375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13375 : oddCount 13375 15 = 9 ∧ acceleratedOrbit 15 13375 = 8036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13375) = 3 ^ 9 * m + 8036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13375.1, data_15_13375.2]

/-- Complete interval computation for depth 15, residue 13376. -/
theorem bounds_15_13376 : exactInterval 15 13376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13376 : oddCount 13376 15 = 5 ∧ acceleratedOrbit 15 13376 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13376) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13376.1, data_15_13376.2]

/-- Complete interval computation for depth 15, residue 13377. -/
theorem bounds_15_13377 : exactInterval 15 13377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13377 : oddCount 13377 15 = 6 ∧ acceleratedOrbit 15 13377 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13377) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13377.1, data_15_13377.2]

/-- Complete interval computation for depth 15, residue 13378. -/
theorem bounds_15_13378 : exactInterval 15 13378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13378 : oddCount 13378 15 = 6 ∧ acceleratedOrbit 15 13378 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13378) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13378.1, data_15_13378.2]

/-- Complete interval computation for depth 15, residue 13379. -/
theorem bounds_15_13379 : exactInterval 15 13379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13379 : oddCount 13379 15 = 6 ∧ acceleratedOrbit 15 13379 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13379) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13379.1, data_15_13379.2]

/-- Complete interval computation for depth 15, residue 13380. -/
theorem bounds_15_13380 : exactInterval 15 13380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13380 : oddCount 13380 15 = 6 ∧ acceleratedOrbit 15 13380 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13380) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13380.1, data_15_13380.2]

/-- Complete interval computation for depth 15, residue 13381. -/
theorem bounds_15_13381 : exactInterval 15 13381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13381 : oddCount 13381 15 = 6 ∧ acceleratedOrbit 15 13381 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13381) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13381.1, data_15_13381.2]

/-- Complete interval computation for depth 15, residue 13382. -/
theorem bounds_15_13382 : exactInterval 15 13382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13382 : oddCount 13382 15 = 6 ∧ acceleratedOrbit 15 13382 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13382) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13382.1, data_15_13382.2]

/-- Complete interval computation for depth 15, residue 13383. -/
theorem bounds_15_13383 : exactInterval 15 13383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13383 : oddCount 13383 15 = 8 ∧ acceleratedOrbit 15 13383 = 2680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13383) = 3 ^ 8 * m + 2680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13383.1, data_15_13383.2]

/-- Complete interval computation for depth 15, residue 13384. -/
theorem bounds_15_13384 : exactInterval 15 13384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13384 : oddCount 13384 15 = 8 ∧ acceleratedOrbit 15 13384 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13384) = 3 ^ 8 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13384.1, data_15_13384.2]

/-- Complete interval computation for depth 15, residue 13385. -/
theorem bounds_15_13385 : exactInterval 15 13385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13385 : oddCount 13385 15 = 8 ∧ acceleratedOrbit 15 13385 = 2681 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13385) = 3 ^ 8 * m + 2681 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13385.1, data_15_13385.2]

/-- Complete interval computation for depth 15, residue 13386. -/
theorem bounds_15_13386 : exactInterval 15 13386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13386 : oddCount 13386 15 = 8 ∧ acceleratedOrbit 15 13386 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13386) = 3 ^ 8 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13386.1, data_15_13386.2]

/-- Complete interval computation for depth 15, residue 13387. -/
theorem bounds_15_13387 : exactInterval 15 13387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13387 : oddCount 13387 15 = 6 ∧ acceleratedOrbit 15 13387 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13387) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13387.1, data_15_13387.2]

/-- Complete interval computation for depth 15, residue 13388. -/
theorem bounds_15_13388 : exactInterval 15 13388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13388 : oddCount 13388 15 = 8 ∧ acceleratedOrbit 15 13388 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13388) = 3 ^ 8 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13388.1, data_15_13388.2]

/-- Complete interval computation for depth 15, residue 13389. -/
theorem bounds_15_13389 : exactInterval 15 13389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13389 : oddCount 13389 15 = 8 ∧ acceleratedOrbit 15 13389 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13389) = 3 ^ 8 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13389.1, data_15_13389.2]

/-- Complete interval computation for depth 15, residue 13390. -/
theorem bounds_15_13390 : exactInterval 15 13390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13390 : oddCount 13390 15 = 6 ∧ acceleratedOrbit 15 13390 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13390) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13390.1, data_15_13390.2]

/-- Complete interval computation for depth 15, residue 13391. -/
theorem bounds_15_13391 : exactInterval 15 13391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13391 : oddCount 13391 15 = 6 ∧ acceleratedOrbit 15 13391 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13391) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13391.1, data_15_13391.2]

/-- Complete interval computation for depth 15, residue 13392. -/
theorem bounds_15_13392 : exactInterval 15 13392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13392 : oddCount 13392 15 = 5 ∧ acceleratedOrbit 15 13392 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13392) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13392.1, data_15_13392.2]

/-- Complete interval computation for depth 15, residue 13393. -/
theorem bounds_15_13393 : exactInterval 15 13393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13393 : oddCount 13393 15 = 8 ∧ acceleratedOrbit 15 13393 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13393) = 3 ^ 8 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13393.1, data_15_13393.2]

/-- Complete interval computation for depth 15, residue 13394. -/
theorem bounds_15_13394 : exactInterval 15 13394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13394 : oddCount 13394 15 = 9 ∧ acceleratedOrbit 15 13394 = 8048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13394) = 3 ^ 9 * m + 8048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13394.1, data_15_13394.2]

/-- Complete interval computation for depth 15, residue 13395. -/
theorem bounds_15_13395 : exactInterval 15 13395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13395 : oddCount 13395 15 = 9 ∧ acceleratedOrbit 15 13395 = 8048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13395) = 3 ^ 9 * m + 8048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13395.1, data_15_13395.2]

/-- Complete interval computation for depth 15, residue 13396. -/
theorem bounds_15_13396 : exactInterval 15 13396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13396 : oddCount 13396 15 = 5 ∧ acceleratedOrbit 15 13396 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13396) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13396.1, data_15_13396.2]

/-- Complete interval computation for depth 15, residue 13397. -/
theorem bounds_15_13397 : exactInterval 15 13397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13397 : oddCount 13397 15 = 5 ∧ acceleratedOrbit 15 13397 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13397) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13397.1, data_15_13397.2]

/-- Complete interval computation for depth 15, residue 13398. -/
theorem bounds_15_13398 : exactInterval 15 13398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13398 : oddCount 13398 15 = 6 ∧ acceleratedOrbit 15 13398 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13398) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13398.1, data_15_13398.2]

/-- Complete interval computation for depth 15, residue 13399. -/
theorem bounds_15_13399 : exactInterval 15 13399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13399 : oddCount 13399 15 = 6 ∧ acceleratedOrbit 15 13399 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13399) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13399.1, data_15_13399.2]

/-- Complete interval computation for depth 15, residue 13400. -/
theorem bounds_15_13400 : exactInterval 15 13400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13400 : oddCount 13400 15 = 6 ∧ acceleratedOrbit 15 13400 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13400) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13400.1, data_15_13400.2]

/-- Complete interval computation for depth 15, residue 13401. -/
theorem bounds_15_13401 : exactInterval 15 13401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13401 : oddCount 13401 15 = 7 ∧ acceleratedOrbit 15 13401 = 895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13401) = 3 ^ 7 * m + 895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13401.1, data_15_13401.2]

end Collatz.Research.PassageAtlas.Batch0409
