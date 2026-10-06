import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0806

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26378. -/
theorem bounds_15_26378 : exactInterval 15 26378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26378 : oddCount 26378 15 = 8 ∧ acceleratedOrbit 15 26378 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26378) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26378.1, data_15_26378.2]

/-- Complete interval computation for depth 15, residue 26379. -/
theorem bounds_15_26379 : exactInterval 15 26379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26379 : oddCount 26379 15 = 10 ∧ acceleratedOrbit 15 26379 = 47546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26379) = 3 ^ 10 * m + 47546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26379.1, data_15_26379.2]

/-- Complete interval computation for depth 15, residue 26380. -/
theorem bounds_15_26380 : exactInterval 15 26380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26380 : oddCount 26380 15 = 8 ∧ acceleratedOrbit 15 26380 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26380) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26380.1, data_15_26380.2]

/-- Complete interval computation for depth 15, residue 26381. -/
theorem bounds_15_26381 : exactInterval 15 26381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26381 : oddCount 26381 15 = 8 ∧ acceleratedOrbit 15 26381 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26381) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26381.1, data_15_26381.2]

/-- Complete interval computation for depth 15, residue 26382. -/
theorem bounds_15_26382 : exactInterval 15 26382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26382 : oddCount 26382 15 = 8 ∧ acceleratedOrbit 15 26382 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26382) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26382.1, data_15_26382.2]

/-- Complete interval computation for depth 15, residue 26383. -/
theorem bounds_15_26383 : exactInterval 15 26383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26383 : oddCount 26383 15 = 8 ∧ acceleratedOrbit 15 26383 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26383) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26383.1, data_15_26383.2]

/-- Complete interval computation for depth 15, residue 26384. -/
theorem bounds_15_26384 : exactInterval 15 26384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26384 : oddCount 26384 15 = 3 ∧ acceleratedOrbit 15 26384 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26384) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26384.1, data_15_26384.2]

/-- Complete interval computation for depth 15, residue 26385. -/
theorem bounds_15_26385 : exactInterval 15 26385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26385 : oddCount 26385 15 = 8 ∧ acceleratedOrbit 15 26385 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26385) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26385.1, data_15_26385.2]

/-- Complete interval computation for depth 15, residue 26386. -/
theorem bounds_15_26386 : exactInterval 15 26386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26386 : oddCount 26386 15 = 8 ∧ acceleratedOrbit 15 26386 = 5284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26386) = 3 ^ 8 * m + 5284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26386.1, data_15_26386.2]

/-- Complete interval computation for depth 15, residue 26387. -/
theorem bounds_15_26387 : exactInterval 15 26387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26387 : oddCount 26387 15 = 8 ∧ acceleratedOrbit 15 26387 = 5284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26387) = 3 ^ 8 * m + 5284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26387.1, data_15_26387.2]

/-- Complete interval computation for depth 15, residue 26388. -/
theorem bounds_15_26388 : exactInterval 15 26388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26388 : oddCount 26388 15 = 3 ∧ acceleratedOrbit 15 26388 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26388) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26388.1, data_15_26388.2]

/-- Complete interval computation for depth 15, residue 26389. -/
theorem bounds_15_26389 : exactInterval 15 26389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26389 : oddCount 26389 15 = 3 ∧ acceleratedOrbit 15 26389 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26389) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26389.1, data_15_26389.2]

/-- Complete interval computation for depth 15, residue 26390. -/
theorem bounds_15_26390 : exactInterval 15 26390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26390 : oddCount 26390 15 = 10 ∧ acceleratedOrbit 15 26390 = 47567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26390) = 3 ^ 10 * m + 47567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26390.1, data_15_26390.2]

/-- Complete interval computation for depth 15, residue 26391. -/
theorem bounds_15_26391 : exactInterval 15 26391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26391 : oddCount 26391 15 = 10 ∧ acceleratedOrbit 15 26391 = 47567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26391) = 3 ^ 10 * m + 47567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26391.1, data_15_26391.2]

/-- Complete interval computation for depth 15, residue 26392. -/
theorem bounds_15_26392 : exactInterval 15 26392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26392 : oddCount 26392 15 = 3 ∧ acceleratedOrbit 15 26392 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26392) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26392.1, data_15_26392.2]

/-- Complete interval computation for depth 15, residue 26393. -/
theorem bounds_15_26393 : exactInterval 15 26393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26393 : oddCount 26393 15 = 10 ∧ acceleratedOrbit 15 26393 = 47567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26393) = 3 ^ 10 * m + 47567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26393.1, data_15_26393.2]

/-- Complete interval computation for depth 15, residue 26394. -/
theorem bounds_15_26394 : exactInterval 15 26394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26394 : oddCount 26394 15 = 3 ∧ acceleratedOrbit 15 26394 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26394) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26394.1, data_15_26394.2]

/-- Complete interval computation for depth 15, residue 26395. -/
theorem bounds_15_26395 : exactInterval 15 26395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26395 : oddCount 26395 15 = 12 ∧ acceleratedOrbit 15 26395 = 428105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26395) = 3 ^ 12 * m + 428105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26395.1, data_15_26395.2]

/-- Complete interval computation for depth 15, residue 26396. -/
theorem bounds_15_26396 : exactInterval 15 26396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26396 : oddCount 26396 15 = 8 ∧ acceleratedOrbit 15 26396 = 5287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26396) = 3 ^ 8 * m + 5287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26396.1, data_15_26396.2]

/-- Complete interval computation for depth 15, residue 26397. -/
theorem bounds_15_26397 : exactInterval 15 26397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26397 : oddCount 26397 15 = 8 ∧ acceleratedOrbit 15 26397 = 5287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26397) = 3 ^ 8 * m + 5287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26397.1, data_15_26397.2]

/-- Complete interval computation for depth 15, residue 26398. -/
theorem bounds_15_26398 : exactInterval 15 26398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26398 : oddCount 26398 15 = 8 ∧ acceleratedOrbit 15 26398 = 5287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26398) = 3 ^ 8 * m + 5287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26398.1, data_15_26398.2]

/-- Complete interval computation for depth 15, residue 26399. -/
theorem bounds_15_26399 : exactInterval 15 26399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26399 : oddCount 26399 15 = 7 ∧ acceleratedOrbit 15 26399 = 1762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26399) = 3 ^ 7 * m + 1762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26399.1, data_15_26399.2]

/-- Complete interval computation for depth 15, residue 26400. -/
theorem bounds_15_26400 : exactInterval 15 26400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26400 : oddCount 26400 15 = 6 ∧ acceleratedOrbit 15 26400 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26400) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26400.1, data_15_26400.2]

/-- Complete interval computation for depth 15, residue 26401. -/
theorem bounds_15_26401 : exactInterval 15 26401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26401 : oddCount 26401 15 = 7 ∧ acceleratedOrbit 15 26401 = 1763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26401) = 3 ^ 7 * m + 1763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26401.1, data_15_26401.2]

/-- Complete interval computation for depth 15, residue 26402. -/
theorem bounds_15_26402 : exactInterval 15 26402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26402 : oddCount 26402 15 = 8 ∧ acceleratedOrbit 15 26402 = 5291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26402) = 3 ^ 8 * m + 5291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26402.1, data_15_26402.2]

/-- Complete interval computation for depth 15, residue 26403. -/
theorem bounds_15_26403 : exactInterval 15 26403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26403 : oddCount 26403 15 = 8 ∧ acceleratedOrbit 15 26403 = 5291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26403) = 3 ^ 8 * m + 5291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26403.1, data_15_26403.2]

/-- Complete interval computation for depth 15, residue 26404. -/
theorem bounds_15_26404 : exactInterval 15 26404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26404 : oddCount 26404 15 = 8 ∧ acceleratedOrbit 15 26404 = 5291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26404) = 3 ^ 8 * m + 5291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26404.1, data_15_26404.2]

/-- Complete interval computation for depth 15, residue 26405. -/
theorem bounds_15_26405 : exactInterval 15 26405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26405 : oddCount 26405 15 = 8 ∧ acceleratedOrbit 15 26405 = 5291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26405) = 3 ^ 8 * m + 5291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26405.1, data_15_26405.2]

/-- Complete interval computation for depth 15, residue 26406. -/
theorem bounds_15_26406 : exactInterval 15 26406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26406 : oddCount 26406 15 = 8 ∧ acceleratedOrbit 15 26406 = 5291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26406) = 3 ^ 8 * m + 5291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26406.1, data_15_26406.2]

/-- Complete interval computation for depth 15, residue 26407. -/
theorem bounds_15_26407 : exactInterval 15 26407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26407 : oddCount 26407 15 = 10 ∧ acceleratedOrbit 15 26407 = 47591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26407) = 3 ^ 10 * m + 47591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26407.1, data_15_26407.2]

/-- Complete interval computation for depth 15, residue 26408. -/
theorem bounds_15_26408 : exactInterval 15 26408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26408 : oddCount 26408 15 = 6 ∧ acceleratedOrbit 15 26408 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26408) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26408.1, data_15_26408.2]

/-- Complete interval computation for depth 15, residue 26409. -/
theorem bounds_15_26409 : exactInterval 15 26409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26409 : oddCount 26409 15 = 9 ∧ acceleratedOrbit 15 26409 = 15866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26409) = 3 ^ 9 * m + 15866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26409.1, data_15_26409.2]

/-- Complete interval computation for depth 15, residue 26410. -/
theorem bounds_15_26410 : exactInterval 15 26410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26410 : oddCount 26410 15 = 6 ∧ acceleratedOrbit 15 26410 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26410) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26410.1, data_15_26410.2]

end Collatz.Research.PassageAtlas.Batch0806
