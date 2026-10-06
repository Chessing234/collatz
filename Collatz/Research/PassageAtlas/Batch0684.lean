import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0684

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22380. -/
theorem bounds_15_22380 : exactInterval 15 22380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22380 : oddCount 22380 15 = 5 ∧ acceleratedOrbit 15 22380 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22380) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22380.1, data_15_22380.2]

/-- Complete interval computation for depth 15, residue 22381. -/
theorem bounds_15_22381 : exactInterval 15 22381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22381 : oddCount 22381 15 = 5 ∧ acceleratedOrbit 15 22381 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22381) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22381.1, data_15_22381.2]

/-- Complete interval computation for depth 15, residue 22382. -/
theorem bounds_15_22382 : exactInterval 15 22382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22382 : oddCount 22382 15 = 5 ∧ acceleratedOrbit 15 22382 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22382) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22382.1, data_15_22382.2]

/-- Complete interval computation for depth 15, residue 22383. -/
theorem bounds_15_22383 : exactInterval 15 22383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22383 : oddCount 22383 15 = 12 ∧ acceleratedOrbit 15 22383 = 363041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22383) = 3 ^ 12 * m + 363041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22383.1, data_15_22383.2]

/-- Complete interval computation for depth 15, residue 22384. -/
theorem bounds_15_22384 : exactInterval 15 22384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22384 : oddCount 22384 15 = 6 ∧ acceleratedOrbit 15 22384 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22384) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22384.1, data_15_22384.2]

/-- Complete interval computation for depth 15, residue 22385. -/
theorem bounds_15_22385 : exactInterval 15 22385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22385 : oddCount 22385 15 = 6 ∧ acceleratedOrbit 15 22385 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22385) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22385.1, data_15_22385.2]

/-- Complete interval computation for depth 15, residue 22386. -/
theorem bounds_15_22386 : exactInterval 15 22386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22386 : oddCount 22386 15 = 7 ∧ acceleratedOrbit 15 22386 = 1495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22386) = 3 ^ 7 * m + 1495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22386.1, data_15_22386.2]

/-- Complete interval computation for depth 15, residue 22387. -/
theorem bounds_15_22387 : exactInterval 15 22387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22387 : oddCount 22387 15 = 7 ∧ acceleratedOrbit 15 22387 = 1495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22387) = 3 ^ 7 * m + 1495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22387.1, data_15_22387.2]

/-- Complete interval computation for depth 15, residue 22388. -/
theorem bounds_15_22388 : exactInterval 15 22388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22388 : oddCount 22388 15 = 6 ∧ acceleratedOrbit 15 22388 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22388) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22388.1, data_15_22388.2]

/-- Complete interval computation for depth 15, residue 22389. -/
theorem bounds_15_22389 : exactInterval 15 22389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22389 : oddCount 22389 15 = 6 ∧ acceleratedOrbit 15 22389 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22389) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22389.1, data_15_22389.2]

/-- Complete interval computation for depth 15, residue 22390. -/
theorem bounds_15_22390 : exactInterval 15 22390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22390 : oddCount 22390 15 = 7 ∧ acceleratedOrbit 15 22390 = 1495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22390) = 3 ^ 7 * m + 1495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22390.1, data_15_22390.2]

/-- Complete interval computation for depth 15, residue 22391. -/
theorem bounds_15_22391 : exactInterval 15 22391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22391 : oddCount 22391 15 = 7 ∧ acceleratedOrbit 15 22391 = 1495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22391) = 3 ^ 7 * m + 1495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22391.1, data_15_22391.2]

/-- Complete interval computation for depth 15, residue 22392. -/
theorem bounds_15_22392 : exactInterval 15 22392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22392 : oddCount 22392 15 = 9 ∧ acceleratedOrbit 15 22392 = 13456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22392) = 3 ^ 9 * m + 13456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22392.1, data_15_22392.2]

/-- Complete interval computation for depth 15, residue 22393. -/
theorem bounds_15_22393 : exactInterval 15 22393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22393 : oddCount 22393 15 = 10 ∧ acceleratedOrbit 15 22393 = 40358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22393) = 3 ^ 10 * m + 40358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22393.1, data_15_22393.2]

/-- Complete interval computation for depth 15, residue 22394. -/
theorem bounds_15_22394 : exactInterval 15 22394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22394 : oddCount 22394 15 = 9 ∧ acceleratedOrbit 15 22394 = 13456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22394) = 3 ^ 9 * m + 13456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22394.1, data_15_22394.2]

/-- Complete interval computation for depth 15, residue 22395. -/
theorem bounds_15_22395 : exactInterval 15 22395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22395 : oddCount 22395 15 = 9 ∧ acceleratedOrbit 15 22395 = 13454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22395) = 3 ^ 9 * m + 13454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22395.1, data_15_22395.2]

/-- Complete interval computation for depth 15, residue 22396. -/
theorem bounds_15_22396 : exactInterval 15 22396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22396 : oddCount 22396 15 = 9 ∧ acceleratedOrbit 15 22396 = 13456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22396) = 3 ^ 9 * m + 13456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22396.1, data_15_22396.2]

/-- Complete interval computation for depth 15, residue 22397. -/
theorem bounds_15_22397 : exactInterval 15 22397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22397 : oddCount 22397 15 = 9 ∧ acceleratedOrbit 15 22397 = 13456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22397) = 3 ^ 9 * m + 13456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22397.1, data_15_22397.2]

/-- Complete interval computation for depth 15, residue 22398. -/
theorem bounds_15_22398 : exactInterval 15 22398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22398 : oddCount 22398 15 = 10 ∧ acceleratedOrbit 15 22398 = 40366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22398) = 3 ^ 10 * m + 40366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22398.1, data_15_22398.2]

/-- Complete interval computation for depth 15, residue 22399. -/
theorem bounds_15_22399 : exactInterval 15 22399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22399 : oddCount 22399 15 = 10 ∧ acceleratedOrbit 15 22399 = 40366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22399) = 3 ^ 10 * m + 40366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22399.1, data_15_22399.2]

/-- Complete interval computation for depth 15, residue 22400. -/
theorem bounds_15_22400 : exactInterval 15 22400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22400 : oddCount 22400 15 = 5 ∧ acceleratedOrbit 15 22400 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22400) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22400.1, data_15_22400.2]

/-- Complete interval computation for depth 15, residue 22401. -/
theorem bounds_15_22401 : exactInterval 15 22401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22401 : oddCount 22401 15 = 9 ∧ acceleratedOrbit 15 22401 = 13459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22401) = 3 ^ 9 * m + 13459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22401.1, data_15_22401.2]

/-- Complete interval computation for depth 15, residue 22402. -/
theorem bounds_15_22402 : exactInterval 15 22402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22402 : oddCount 22402 15 = 7 ∧ acceleratedOrbit 15 22402 = 1496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22402) = 3 ^ 7 * m + 1496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22402.1, data_15_22402.2]

/-- Complete interval computation for depth 15, residue 22403. -/
theorem bounds_15_22403 : exactInterval 15 22403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22403 : oddCount 22403 15 = 7 ∧ acceleratedOrbit 15 22403 = 1496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22403) = 3 ^ 7 * m + 1496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22403.1, data_15_22403.2]

/-- Complete interval computation for depth 15, residue 22404. -/
theorem bounds_15_22404 : exactInterval 15 22404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22404 : oddCount 22404 15 = 7 ∧ acceleratedOrbit 15 22404 = 1496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22404) = 3 ^ 7 * m + 1496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22404.1, data_15_22404.2]

/-- Complete interval computation for depth 15, residue 22405. -/
theorem bounds_15_22405 : exactInterval 15 22405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22405 : oddCount 22405 15 = 7 ∧ acceleratedOrbit 15 22405 = 1496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22405) = 3 ^ 7 * m + 1496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22405.1, data_15_22405.2]

/-- Complete interval computation for depth 15, residue 22406. -/
theorem bounds_15_22406 : exactInterval 15 22406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22406 : oddCount 22406 15 = 7 ∧ acceleratedOrbit 15 22406 = 1496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22406) = 3 ^ 7 * m + 1496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22406.1, data_15_22406.2]

/-- Complete interval computation for depth 15, residue 22407. -/
theorem bounds_15_22407 : exactInterval 15 22407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22407 : oddCount 22407 15 = 7 ∧ acceleratedOrbit 15 22407 = 1496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22407) = 3 ^ 7 * m + 1496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22407.1, data_15_22407.2]

/-- Complete interval computation for depth 15, residue 22408. -/
theorem bounds_15_22408 : exactInterval 15 22408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22408 : oddCount 22408 15 = 4 ∧ acceleratedOrbit 15 22408 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22408) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22408.1, data_15_22408.2]

/-- Complete interval computation for depth 15, residue 22409. -/
theorem bounds_15_22409 : exactInterval 15 22409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22409 : oddCount 22409 15 = 9 ∧ acceleratedOrbit 15 22409 = 13463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22409) = 3 ^ 9 * m + 13463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22409.1, data_15_22409.2]

/-- Complete interval computation for depth 15, residue 22410. -/
theorem bounds_15_22410 : exactInterval 15 22410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22410 : oddCount 22410 15 = 4 ∧ acceleratedOrbit 15 22410 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22410) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22410.1, data_15_22410.2]

/-- Complete interval computation for depth 15, residue 22411. -/
theorem bounds_15_22411 : exactInterval 15 22411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22411 : oddCount 22411 15 = 11 ∧ acceleratedOrbit 15 22411 = 121175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22411) = 3 ^ 11 * m + 121175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22411.1, data_15_22411.2]

/-- Complete interval computation for depth 15, residue 22412. -/
theorem bounds_15_22412 : exactInterval 15 22412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22412 : oddCount 22412 15 = 4 ∧ acceleratedOrbit 15 22412 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22412) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22412.1, data_15_22412.2]

end Collatz.Research.PassageAtlas.Batch0684
