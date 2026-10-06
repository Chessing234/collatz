import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0348

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11370. -/
theorem bounds_15_11370 : exactInterval 15 11370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11370 : oddCount 11370 15 = 4 ∧ acceleratedOrbit 15 11370 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11370) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11370.1, data_15_11370.2]

/-- Complete interval computation for depth 15, residue 11371. -/
theorem bounds_15_11371 : exactInterval 15 11371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11371 : oddCount 11371 15 = 9 ∧ acceleratedOrbit 15 11371 = 6832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11371) = 3 ^ 9 * m + 6832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11371.1, data_15_11371.2]

/-- Complete interval computation for depth 15, residue 11372. -/
theorem bounds_15_11372 : exactInterval 15 11372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11372 : oddCount 11372 15 = 10 ∧ acceleratedOrbit 15 11372 = 20503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11372) = 3 ^ 10 * m + 20503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11372.1, data_15_11372.2]

/-- Complete interval computation for depth 15, residue 11373. -/
theorem bounds_15_11373 : exactInterval 15 11373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11373 : oddCount 11373 15 = 10 ∧ acceleratedOrbit 15 11373 = 20503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11373) = 3 ^ 10 * m + 20503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11373.1, data_15_11373.2]

/-- Complete interval computation for depth 15, residue 11374. -/
theorem bounds_15_11374 : exactInterval 15 11374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11374 : oddCount 11374 15 = 10 ∧ acceleratedOrbit 15 11374 = 20503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11374) = 3 ^ 10 * m + 20503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11374.1, data_15_11374.2]

/-- Complete interval computation for depth 15, residue 11375. -/
theorem bounds_15_11375 : exactInterval 15 11375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11375 : oddCount 11375 15 = 10 ∧ acceleratedOrbit 15 11375 = 20501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11375) = 3 ^ 10 * m + 20501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11375.1, data_15_11375.2]

/-- Complete interval computation for depth 15, residue 11376. -/
theorem bounds_15_11376 : exactInterval 15 11376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11376 : oddCount 11376 15 = 6 ∧ acceleratedOrbit 15 11376 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11376) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11376.1, data_15_11376.2]

/-- Complete interval computation for depth 15, residue 11377. -/
theorem bounds_15_11377 : exactInterval 15 11377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11377 : oddCount 11377 15 = 4 ∧ acceleratedOrbit 15 11377 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11377) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11377.1, data_15_11377.2]

/-- Complete interval computation for depth 15, residue 11378. -/
theorem bounds_15_11378 : exactInterval 15 11378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11378 : oddCount 11378 15 = 7 ∧ acceleratedOrbit 15 11378 = 760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11378) = 3 ^ 7 * m + 760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11378.1, data_15_11378.2]

/-- Complete interval computation for depth 15, residue 11379. -/
theorem bounds_15_11379 : exactInterval 15 11379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11379 : oddCount 11379 15 = 7 ∧ acceleratedOrbit 15 11379 = 760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11379) = 3 ^ 7 * m + 760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11379.1, data_15_11379.2]

/-- Complete interval computation for depth 15, residue 11380. -/
theorem bounds_15_11380 : exactInterval 15 11380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11380 : oddCount 11380 15 = 6 ∧ acceleratedOrbit 15 11380 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11380) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11380.1, data_15_11380.2]

/-- Complete interval computation for depth 15, residue 11381. -/
theorem bounds_15_11381 : exactInterval 15 11381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11381 : oddCount 11381 15 = 6 ∧ acceleratedOrbit 15 11381 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11381) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11381.1, data_15_11381.2]

/-- Complete interval computation for depth 15, residue 11382. -/
theorem bounds_15_11382 : exactInterval 15 11382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11382 : oddCount 11382 15 = 8 ∧ acceleratedOrbit 15 11382 = 2281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11382) = 3 ^ 8 * m + 2281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11382.1, data_15_11382.2]

/-- Complete interval computation for depth 15, residue 11383. -/
theorem bounds_15_11383 : exactInterval 15 11383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11383 : oddCount 11383 15 = 8 ∧ acceleratedOrbit 15 11383 = 2281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11383) = 3 ^ 8 * m + 2281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11383.1, data_15_11383.2]

/-- Complete interval computation for depth 15, residue 11384. -/
theorem bounds_15_11384 : exactInterval 15 11384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11384 : oddCount 11384 15 = 6 ∧ acceleratedOrbit 15 11384 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11384) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11384.1, data_15_11384.2]

/-- Complete interval computation for depth 15, residue 11385. -/
theorem bounds_15_11385 : exactInterval 15 11385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11385 : oddCount 11385 15 = 7 ∧ acceleratedOrbit 15 11385 = 760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11385) = 3 ^ 7 * m + 760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11385.1, data_15_11385.2]

/-- Complete interval computation for depth 15, residue 11386. -/
theorem bounds_15_11386 : exactInterval 15 11386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11386 : oddCount 11386 15 = 6 ∧ acceleratedOrbit 15 11386 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11386) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11386.1, data_15_11386.2]

/-- Complete interval computation for depth 15, residue 11387. -/
theorem bounds_15_11387 : exactInterval 15 11387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11387 : oddCount 11387 15 = 8 ∧ acceleratedOrbit 15 11387 = 2281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11387) = 3 ^ 8 * m + 2281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11387.1, data_15_11387.2]

/-- Complete interval computation for depth 15, residue 11388. -/
theorem bounds_15_11388 : exactInterval 15 11388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11388 : oddCount 11388 15 = 9 ∧ acceleratedOrbit 15 11388 = 6844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11388) = 3 ^ 9 * m + 6844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11388.1, data_15_11388.2]

/-- Complete interval computation for depth 15, residue 11389. -/
theorem bounds_15_11389 : exactInterval 15 11389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11389 : oddCount 11389 15 = 9 ∧ acceleratedOrbit 15 11389 = 6844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11389) = 3 ^ 9 * m + 6844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11389.1, data_15_11389.2]

/-- Complete interval computation for depth 15, residue 11390. -/
theorem bounds_15_11390 : exactInterval 15 11390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11390 : oddCount 11390 15 = 9 ∧ acceleratedOrbit 15 11390 = 6844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11390) = 3 ^ 9 * m + 6844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11390.1, data_15_11390.2]

/-- Complete interval computation for depth 15, residue 11391. -/
theorem bounds_15_11391 : exactInterval 15 11391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11391 : oddCount 11391 15 = 13 ∧ acceleratedOrbit 15 11391 = 554282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11391) = 3 ^ 13 * m + 554282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11391.1, data_15_11391.2]

/-- Complete interval computation for depth 15, residue 11392. -/
theorem bounds_15_11392 : exactInterval 15 11392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11392 : oddCount 11392 15 = 4 ∧ acceleratedOrbit 15 11392 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11392) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11392.1, data_15_11392.2]

/-- Complete interval computation for depth 15, residue 11393. -/
theorem bounds_15_11393 : exactInterval 15 11393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11393 : oddCount 11393 15 = 8 ∧ acceleratedOrbit 15 11393 = 2282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11393) = 3 ^ 8 * m + 2282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11393.1, data_15_11393.2]

/-- Complete interval computation for depth 15, residue 11394. -/
theorem bounds_15_11394 : exactInterval 15 11394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11394 : oddCount 11394 15 = 6 ∧ acceleratedOrbit 15 11394 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11394) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11394.1, data_15_11394.2]

/-- Complete interval computation for depth 15, residue 11395. -/
theorem bounds_15_11395 : exactInterval 15 11395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11395 : oddCount 11395 15 = 6 ∧ acceleratedOrbit 15 11395 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11395) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11395.1, data_15_11395.2]

/-- Complete interval computation for depth 15, residue 11396. -/
theorem bounds_15_11396 : exactInterval 15 11396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11396 : oddCount 11396 15 = 6 ∧ acceleratedOrbit 15 11396 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11396) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11396.1, data_15_11396.2]

/-- Complete interval computation for depth 15, residue 11397. -/
theorem bounds_15_11397 : exactInterval 15 11397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11397 : oddCount 11397 15 = 6 ∧ acceleratedOrbit 15 11397 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11397) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11397.1, data_15_11397.2]

/-- Complete interval computation for depth 15, residue 11398. -/
theorem bounds_15_11398 : exactInterval 15 11398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11398 : oddCount 11398 15 = 6 ∧ acceleratedOrbit 15 11398 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11398) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11398.1, data_15_11398.2]

/-- Complete interval computation for depth 15, residue 11399. -/
theorem bounds_15_11399 : exactInterval 15 11399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11399 : oddCount 11399 15 = 7 ∧ acceleratedOrbit 15 11399 = 761 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11399) = 3 ^ 7 * m + 761 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11399.1, data_15_11399.2]

/-- Complete interval computation for depth 15, residue 11400. -/
theorem bounds_15_11400 : exactInterval 15 11400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11400 : oddCount 11400 15 = 5 ∧ acceleratedOrbit 15 11400 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11400) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11400.1, data_15_11400.2]

/-- Complete interval computation for depth 15, residue 11401. -/
theorem bounds_15_11401 : exactInterval 15 11401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11401 : oddCount 11401 15 = 10 ∧ acceleratedOrbit 15 11401 = 20549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11401) = 3 ^ 10 * m + 20549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11401.1, data_15_11401.2]

/-- Complete interval computation for depth 15, residue 11402. -/
theorem bounds_15_11402 : exactInterval 15 11402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11402 : oddCount 11402 15 = 5 ∧ acceleratedOrbit 15 11402 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11402) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11402.1, data_15_11402.2]

end Collatz.Research.PassageAtlas.Batch0348
