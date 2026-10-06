import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0165

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5373. -/
theorem bounds_15_5373 : exactInterval 15 5373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5373 : oddCount 5373 15 = 9 ∧ acceleratedOrbit 15 5373 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5373) = 3 ^ 9 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5373.1, data_15_5373.2]

/-- Complete interval computation for depth 15, residue 5374. -/
theorem bounds_15_5374 : exactInterval 15 5374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5374 : oddCount 5374 15 = 10 ∧ acceleratedOrbit 15 5374 = 9688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5374) = 3 ^ 10 * m + 9688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5374.1, data_15_5374.2]

/-- Complete interval computation for depth 15, residue 5375. -/
theorem bounds_15_5375 : exactInterval 15 5375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5375 : oddCount 5375 15 = 10 ∧ acceleratedOrbit 15 5375 = 9688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5375) = 3 ^ 10 * m + 9688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5375.1, data_15_5375.2]

/-- Complete interval computation for depth 15, residue 5376. -/
theorem bounds_15_5376 : exactInterval 15 5376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5376 : oddCount 5376 15 = 2 ∧ acceleratedOrbit 15 5376 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5376) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5376.1, data_15_5376.2]

/-- Complete interval computation for depth 15, residue 5377. -/
theorem bounds_15_5377 : exactInterval 15 5377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5377 : oddCount 5377 15 = 8 ∧ acceleratedOrbit 15 5377 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5377) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5377.1, data_15_5377.2]

/-- Complete interval computation for depth 15, residue 5378. -/
theorem bounds_15_5378 : exactInterval 15 5378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5378 : oddCount 5378 15 = 9 ∧ acceleratedOrbit 15 5378 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5378) = 3 ^ 9 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5378.1, data_15_5378.2]

/-- Complete interval computation for depth 15, residue 5379. -/
theorem bounds_15_5379 : exactInterval 15 5379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5379 : oddCount 5379 15 = 9 ∧ acceleratedOrbit 15 5379 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5379) = 3 ^ 9 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5379.1, data_15_5379.2]

/-- Complete interval computation for depth 15, residue 5380. -/
theorem bounds_15_5380 : exactInterval 15 5380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5380 : oddCount 5380 15 = 6 ∧ acceleratedOrbit 15 5380 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5380) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5380.1, data_15_5380.2]

/-- Complete interval computation for depth 15, residue 5381. -/
theorem bounds_15_5381 : exactInterval 15 5381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5381 : oddCount 5381 15 = 6 ∧ acceleratedOrbit 15 5381 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5381) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5381.1, data_15_5381.2]

/-- Complete interval computation for depth 15, residue 5382. -/
theorem bounds_15_5382 : exactInterval 15 5382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5382 : oddCount 5382 15 = 6 ∧ acceleratedOrbit 15 5382 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5382) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5382.1, data_15_5382.2]

/-- Complete interval computation for depth 15, residue 5383. -/
theorem bounds_15_5383 : exactInterval 15 5383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5383 : oddCount 5383 15 = 9 ∧ acceleratedOrbit 15 5383 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5383) = 3 ^ 9 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5383.1, data_15_5383.2]

/-- Complete interval computation for depth 15, residue 5384. -/
theorem bounds_15_5384 : exactInterval 15 5384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5384 : oddCount 5384 15 = 7 ∧ acceleratedOrbit 15 5384 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5384) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5384.1, data_15_5384.2]

/-- Complete interval computation for depth 15, residue 5385. -/
theorem bounds_15_5385 : exactInterval 15 5385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5385 : oddCount 5385 15 = 10 ∧ acceleratedOrbit 15 5385 = 9710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5385) = 3 ^ 10 * m + 9710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5385.1, data_15_5385.2]

/-- Complete interval computation for depth 15, residue 5386. -/
theorem bounds_15_5386 : exactInterval 15 5386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5386 : oddCount 5386 15 = 7 ∧ acceleratedOrbit 15 5386 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5386) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5386.1, data_15_5386.2]

/-- Complete interval computation for depth 15, residue 5387. -/
theorem bounds_15_5387 : exactInterval 15 5387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5387 : oddCount 5387 15 = 10 ∧ acceleratedOrbit 15 5387 = 9719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5387) = 3 ^ 10 * m + 9719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5387.1, data_15_5387.2]

/-- Complete interval computation for depth 15, residue 5388. -/
theorem bounds_15_5388 : exactInterval 15 5388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5388 : oddCount 5388 15 = 7 ∧ acceleratedOrbit 15 5388 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5388) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5388.1, data_15_5388.2]

/-- Complete interval computation for depth 15, residue 5389. -/
theorem bounds_15_5389 : exactInterval 15 5389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5389 : oddCount 5389 15 = 7 ∧ acceleratedOrbit 15 5389 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5389) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5389.1, data_15_5389.2]

/-- Complete interval computation for depth 15, residue 5390. -/
theorem bounds_15_5390 : exactInterval 15 5390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5390 : oddCount 5390 15 = 5 ∧ acceleratedOrbit 15 5390 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5390) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5390.1, data_15_5390.2]

/-- Complete interval computation for depth 15, residue 5391. -/
theorem bounds_15_5391 : exactInterval 15 5391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5391 : oddCount 5391 15 = 5 ∧ acceleratedOrbit 15 5391 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5391) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5391.1, data_15_5391.2]

/-- Complete interval computation for depth 15, residue 5392. -/
theorem bounds_15_5392 : exactInterval 15 5392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5392 : oddCount 5392 15 = 7 ∧ acceleratedOrbit 15 5392 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5392) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5392.1, data_15_5392.2]

/-- Complete interval computation for depth 15, residue 5393. -/
theorem bounds_15_5393 : exactInterval 15 5393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5393 : oddCount 5393 15 = 7 ∧ acceleratedOrbit 15 5393 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5393) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5393.1, data_15_5393.2]

/-- Complete interval computation for depth 15, residue 5394. -/
theorem bounds_15_5394 : exactInterval 15 5394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5394 : oddCount 5394 15 = 8 ∧ acceleratedOrbit 15 5394 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5394) = 3 ^ 8 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5394.1, data_15_5394.2]

/-- Complete interval computation for depth 15, residue 5395. -/
theorem bounds_15_5395 : exactInterval 15 5395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5395 : oddCount 5395 15 = 8 ∧ acceleratedOrbit 15 5395 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5395) = 3 ^ 8 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5395.1, data_15_5395.2]

/-- Complete interval computation for depth 15, residue 5396. -/
theorem bounds_15_5396 : exactInterval 15 5396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5396 : oddCount 5396 15 = 7 ∧ acceleratedOrbit 15 5396 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5396) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5396.1, data_15_5396.2]

/-- Complete interval computation for depth 15, residue 5397. -/
theorem bounds_15_5397 : exactInterval 15 5397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5397 : oddCount 5397 15 = 7 ∧ acceleratedOrbit 15 5397 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5397) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5397.1, data_15_5397.2]

/-- Complete interval computation for depth 15, residue 5398. -/
theorem bounds_15_5398 : exactInterval 15 5398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5398 : oddCount 5398 15 = 7 ∧ acceleratedOrbit 15 5398 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5398) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5398.1, data_15_5398.2]

/-- Complete interval computation for depth 15, residue 5399. -/
theorem bounds_15_5399 : exactInterval 15 5399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5399 : oddCount 5399 15 = 7 ∧ acceleratedOrbit 15 5399 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5399) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5399.1, data_15_5399.2]

/-- Complete interval computation for depth 15, residue 5400. -/
theorem bounds_15_5400 : exactInterval 15 5400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5400 : oddCount 5400 15 = 7 ∧ acceleratedOrbit 15 5400 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5400) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5400.1, data_15_5400.2]

/-- Complete interval computation for depth 15, residue 5401. -/
theorem bounds_15_5401 : exactInterval 15 5401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5401 : oddCount 5401 15 = 10 ∧ acceleratedOrbit 15 5401 = 9740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5401) = 3 ^ 10 * m + 9740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5401.1, data_15_5401.2]

/-- Complete interval computation for depth 15, residue 5402. -/
theorem bounds_15_5402 : exactInterval 15 5402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5402 : oddCount 5402 15 = 7 ∧ acceleratedOrbit 15 5402 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5402) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5402.1, data_15_5402.2]

/-- Complete interval computation for depth 15, residue 5403. -/
theorem bounds_15_5403 : exactInterval 15 5403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5403 : oddCount 5403 15 = 10 ∧ acceleratedOrbit 15 5403 = 9739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5403) = 3 ^ 10 * m + 9739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5403.1, data_15_5403.2]

/-- Complete interval computation for depth 15, residue 5404. -/
theorem bounds_15_5404 : exactInterval 15 5404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5404 : oddCount 5404 15 = 9 ∧ acceleratedOrbit 15 5404 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5404) = 3 ^ 9 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5404.1, data_15_5404.2]

/-- Complete interval computation for depth 15, residue 5405. -/
theorem bounds_15_5405 : exactInterval 15 5405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5405 : oddCount 5405 15 = 9 ∧ acceleratedOrbit 15 5405 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5405) = 3 ^ 9 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5405.1, data_15_5405.2]

end Collatz.Research.PassageAtlas.Batch0165
