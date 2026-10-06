import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0226

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7372. -/
theorem bounds_15_7372 : exactInterval 15 7372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7372 : oddCount 7372 15 = 5 ∧ acceleratedOrbit 15 7372 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7372) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7372.1, data_15_7372.2]

/-- Complete interval computation for depth 15, residue 7373. -/
theorem bounds_15_7373 : exactInterval 15 7373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7373 : oddCount 7373 15 = 5 ∧ acceleratedOrbit 15 7373 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7373) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7373.1, data_15_7373.2]

/-- Complete interval computation for depth 15, residue 7374. -/
theorem bounds_15_7374 : exactInterval 15 7374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7374 : oddCount 7374 15 = 8 ∧ acceleratedOrbit 15 7374 = 1477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7374) = 3 ^ 8 * m + 1477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7374.1, data_15_7374.2]

/-- Complete interval computation for depth 15, residue 7375. -/
theorem bounds_15_7375 : exactInterval 15 7375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7375 : oddCount 7375 15 = 8 ∧ acceleratedOrbit 15 7375 = 1477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7375) = 3 ^ 8 * m + 1477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7375.1, data_15_7375.2]

/-- Complete interval computation for depth 15, residue 7376. -/
theorem bounds_15_7376 : exactInterval 15 7376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7376 : oddCount 7376 15 = 5 ∧ acceleratedOrbit 15 7376 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7376) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7376.1, data_15_7376.2]

/-- Complete interval computation for depth 15, residue 7377. -/
theorem bounds_15_7377 : exactInterval 15 7377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7377 : oddCount 7377 15 = 10 ∧ acceleratedOrbit 15 7377 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7377) = 3 ^ 10 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7377.1, data_15_7377.2]

/-- Complete interval computation for depth 15, residue 7378. -/
theorem bounds_15_7378 : exactInterval 15 7378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7378 : oddCount 7378 15 = 10 ∧ acceleratedOrbit 15 7378 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7378) = 3 ^ 10 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7378.1, data_15_7378.2]

/-- Complete interval computation for depth 15, residue 7379. -/
theorem bounds_15_7379 : exactInterval 15 7379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7379 : oddCount 7379 15 = 10 ∧ acceleratedOrbit 15 7379 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7379) = 3 ^ 10 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7379.1, data_15_7379.2]

/-- Complete interval computation for depth 15, residue 7380. -/
theorem bounds_15_7380 : exactInterval 15 7380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7380 : oddCount 7380 15 = 5 ∧ acceleratedOrbit 15 7380 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7380) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7380.1, data_15_7380.2]

/-- Complete interval computation for depth 15, residue 7381. -/
theorem bounds_15_7381 : exactInterval 15 7381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7381 : oddCount 7381 15 = 5 ∧ acceleratedOrbit 15 7381 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7381) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7381.1, data_15_7381.2]

/-- Complete interval computation for depth 15, residue 7382. -/
theorem bounds_15_7382 : exactInterval 15 7382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7382 : oddCount 7382 15 = 7 ∧ acceleratedOrbit 15 7382 = 493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7382) = 3 ^ 7 * m + 493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7382.1, data_15_7382.2]

/-- Complete interval computation for depth 15, residue 7383. -/
theorem bounds_15_7383 : exactInterval 15 7383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7383 : oddCount 7383 15 = 7 ∧ acceleratedOrbit 15 7383 = 493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7383) = 3 ^ 7 * m + 493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7383.1, data_15_7383.2]

/-- Complete interval computation for depth 15, residue 7384. -/
theorem bounds_15_7384 : exactInterval 15 7384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7384 : oddCount 7384 15 = 7 ∧ acceleratedOrbit 15 7384 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7384) = 3 ^ 7 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7384.1, data_15_7384.2]

/-- Complete interval computation for depth 15, residue 7385. -/
theorem bounds_15_7385 : exactInterval 15 7385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7385 : oddCount 7385 15 = 7 ∧ acceleratedOrbit 15 7385 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7385) = 3 ^ 7 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7385.1, data_15_7385.2]

/-- Complete interval computation for depth 15, residue 7386. -/
theorem bounds_15_7386 : exactInterval 15 7386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7386 : oddCount 7386 15 = 7 ∧ acceleratedOrbit 15 7386 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7386) = 3 ^ 7 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7386.1, data_15_7386.2]

/-- Complete interval computation for depth 15, residue 7387. -/
theorem bounds_15_7387 : exactInterval 15 7387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7387 : oddCount 7387 15 = 8 ∧ acceleratedOrbit 15 7387 = 1480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7387) = 3 ^ 8 * m + 1480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7387.1, data_15_7387.2]

/-- Complete interval computation for depth 15, residue 7388. -/
theorem bounds_15_7388 : exactInterval 15 7388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7388 : oddCount 7388 15 = 7 ∧ acceleratedOrbit 15 7388 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7388) = 3 ^ 7 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7388.1, data_15_7388.2]

/-- Complete interval computation for depth 15, residue 7389. -/
theorem bounds_15_7389 : exactInterval 15 7389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7389 : oddCount 7389 15 = 7 ∧ acceleratedOrbit 15 7389 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7389) = 3 ^ 7 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7389.1, data_15_7389.2]

/-- Complete interval computation for depth 15, residue 7390. -/
theorem bounds_15_7390 : exactInterval 15 7390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7390 : oddCount 7390 15 = 9 ∧ acceleratedOrbit 15 7390 = 4441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7390) = 3 ^ 9 * m + 4441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7390.1, data_15_7390.2]

/-- Complete interval computation for depth 15, residue 7391. -/
theorem bounds_15_7391 : exactInterval 15 7391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7391 : oddCount 7391 15 = 9 ∧ acceleratedOrbit 15 7391 = 4441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7391) = 3 ^ 9 * m + 4441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7391.1, data_15_7391.2]

/-- Complete interval computation for depth 15, residue 7392. -/
theorem bounds_15_7392 : exactInterval 15 7392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7392 : oddCount 7392 15 = 7 ∧ acceleratedOrbit 15 7392 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7392) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7392.1, data_15_7392.2]

/-- Complete interval computation for depth 15, residue 7393. -/
theorem bounds_15_7393 : exactInterval 15 7393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7393 : oddCount 7393 15 = 10 ∧ acceleratedOrbit 15 7393 = 13328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7393) = 3 ^ 10 * m + 13328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7393.1, data_15_7393.2]

/-- Complete interval computation for depth 15, residue 7394. -/
theorem bounds_15_7394 : exactInterval 15 7394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7394 : oddCount 7394 15 = 5 ∧ acceleratedOrbit 15 7394 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7394) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7394.1, data_15_7394.2]

/-- Complete interval computation for depth 15, residue 7395. -/
theorem bounds_15_7395 : exactInterval 15 7395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7395 : oddCount 7395 15 = 5 ∧ acceleratedOrbit 15 7395 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7395) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7395.1, data_15_7395.2]

/-- Complete interval computation for depth 15, residue 7396. -/
theorem bounds_15_7396 : exactInterval 15 7396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7396 : oddCount 7396 15 = 8 ∧ acceleratedOrbit 15 7396 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7396) = 3 ^ 8 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7396.1, data_15_7396.2]

/-- Complete interval computation for depth 15, residue 7397. -/
theorem bounds_15_7397 : exactInterval 15 7397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7397 : oddCount 7397 15 = 8 ∧ acceleratedOrbit 15 7397 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7397) = 3 ^ 8 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7397.1, data_15_7397.2]

/-- Complete interval computation for depth 15, residue 7398. -/
theorem bounds_15_7398 : exactInterval 15 7398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7398 : oddCount 7398 15 = 8 ∧ acceleratedOrbit 15 7398 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7398) = 3 ^ 8 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7398.1, data_15_7398.2]

/-- Complete interval computation for depth 15, residue 7399. -/
theorem bounds_15_7399 : exactInterval 15 7399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7399 : oddCount 7399 15 = 10 ∧ acceleratedOrbit 15 7399 = 13337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7399) = 3 ^ 10 * m + 13337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7399.1, data_15_7399.2]

/-- Complete interval computation for depth 15, residue 7400. -/
theorem bounds_15_7400 : exactInterval 15 7400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7400 : oddCount 7400 15 = 7 ∧ acceleratedOrbit 15 7400 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7400) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7400.1, data_15_7400.2]

/-- Complete interval computation for depth 15, residue 7401. -/
theorem bounds_15_7401 : exactInterval 15 7401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7401 : oddCount 7401 15 = 9 ∧ acceleratedOrbit 15 7401 = 4448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7401) = 3 ^ 9 * m + 4448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7401.1, data_15_7401.2]

/-- Complete interval computation for depth 15, residue 7402. -/
theorem bounds_15_7402 : exactInterval 15 7402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7402 : oddCount 7402 15 = 7 ∧ acceleratedOrbit 15 7402 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7402) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7402.1, data_15_7402.2]

/-- Complete interval computation for depth 15, residue 7403. -/
theorem bounds_15_7403 : exactInterval 15 7403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7403 : oddCount 7403 15 = 11 ∧ acceleratedOrbit 15 7403 = 40034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7403) = 3 ^ 11 * m + 40034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7403.1, data_15_7403.2]

/-- Complete interval computation for depth 15, residue 7404. -/
theorem bounds_15_7404 : exactInterval 15 7404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7404 : oddCount 7404 15 = 5 ∧ acceleratedOrbit 15 7404 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7404) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7404.1, data_15_7404.2]

end Collatz.Research.PassageAtlas.Batch0226
