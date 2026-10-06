import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0989

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32374. -/
theorem bounds_15_32374 : exactInterval 15 32374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32374 : oddCount 32374 15 = 7 ∧ acceleratedOrbit 15 32374 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32374) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32374.1, data_15_32374.2]

/-- Complete interval computation for depth 15, residue 32375. -/
theorem bounds_15_32375 : exactInterval 15 32375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32375 : oddCount 32375 15 = 7 ∧ acceleratedOrbit 15 32375 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32375) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32375.1, data_15_32375.2]

/-- Complete interval computation for depth 15, residue 32376. -/
theorem bounds_15_32376 : exactInterval 15 32376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32376 : oddCount 32376 15 = 7 ∧ acceleratedOrbit 15 32376 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32376) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32376.1, data_15_32376.2]

/-- Complete interval computation for depth 15, residue 32377. -/
theorem bounds_15_32377 : exactInterval 15 32377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32377 : oddCount 32377 15 = 9 ∧ acceleratedOrbit 15 32377 = 19450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32377) = 3 ^ 9 * m + 19450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32377.1, data_15_32377.2]

/-- Complete interval computation for depth 15, residue 32378. -/
theorem bounds_15_32378 : exactInterval 15 32378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32378 : oddCount 32378 15 = 7 ∧ acceleratedOrbit 15 32378 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32378) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32378.1, data_15_32378.2]

/-- Complete interval computation for depth 15, residue 32379. -/
theorem bounds_15_32379 : exactInterval 15 32379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32379 : oddCount 32379 15 = 7 ∧ acceleratedOrbit 15 32379 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32379) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32379.1, data_15_32379.2]

/-- Complete interval computation for depth 15, residue 32380. -/
theorem bounds_15_32380 : exactInterval 15 32380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32380 : oddCount 32380 15 = 9 ∧ acceleratedOrbit 15 32380 = 19453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32380) = 3 ^ 9 * m + 19453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32380.1, data_15_32380.2]

/-- Complete interval computation for depth 15, residue 32381. -/
theorem bounds_15_32381 : exactInterval 15 32381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32381 : oddCount 32381 15 = 9 ∧ acceleratedOrbit 15 32381 = 19453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32381) = 3 ^ 9 * m + 19453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32381.1, data_15_32381.2]

/-- Complete interval computation for depth 15, residue 32382. -/
theorem bounds_15_32382 : exactInterval 15 32382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32382 : oddCount 32382 15 = 9 ∧ acceleratedOrbit 15 32382 = 19453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32382) = 3 ^ 9 * m + 19453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32382.1, data_15_32382.2]

/-- Complete interval computation for depth 15, residue 32383. -/
theorem bounds_15_32383 : exactInterval 15 32383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32383 : oddCount 32383 15 = 12 ∧ acceleratedOrbit 15 32383 = 525214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32383) = 3 ^ 12 * m + 525214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32383.1, data_15_32383.2]

/-- Complete interval computation for depth 15, residue 32384. -/
theorem bounds_15_32384 : exactInterval 15 32384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32384 : oddCount 32384 15 = 6 ∧ acceleratedOrbit 15 32384 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32384) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32384.1, data_15_32384.2]

/-- Complete interval computation for depth 15, residue 32385. -/
theorem bounds_15_32385 : exactInterval 15 32385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32385 : oddCount 32385 15 = 8 ∧ acceleratedOrbit 15 32385 = 6485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32385) = 3 ^ 8 * m + 6485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32385.1, data_15_32385.2]

/-- Complete interval computation for depth 15, residue 32386. -/
theorem bounds_15_32386 : exactInterval 15 32386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32386 : oddCount 32386 15 = 6 ∧ acceleratedOrbit 15 32386 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32386) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32386.1, data_15_32386.2]

/-- Complete interval computation for depth 15, residue 32387. -/
theorem bounds_15_32387 : exactInterval 15 32387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32387 : oddCount 32387 15 = 6 ∧ acceleratedOrbit 15 32387 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32387) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32387.1, data_15_32387.2]

/-- Complete interval computation for depth 15, residue 32388. -/
theorem bounds_15_32388 : exactInterval 15 32388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32388 : oddCount 32388 15 = 6 ∧ acceleratedOrbit 15 32388 = 721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32388) = 3 ^ 6 * m + 721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32388.1, data_15_32388.2]

/-- Complete interval computation for depth 15, residue 32389. -/
theorem bounds_15_32389 : exactInterval 15 32389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32389 : oddCount 32389 15 = 6 ∧ acceleratedOrbit 15 32389 = 721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32389) = 3 ^ 6 * m + 721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32389.1, data_15_32389.2]

/-- Complete interval computation for depth 15, residue 32390. -/
theorem bounds_15_32390 : exactInterval 15 32390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32390 : oddCount 32390 15 = 6 ∧ acceleratedOrbit 15 32390 = 721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32390) = 3 ^ 6 * m + 721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32390.1, data_15_32390.2]

/-- Complete interval computation for depth 15, residue 32391. -/
theorem bounds_15_32391 : exactInterval 15 32391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32391 : oddCount 32391 15 = 9 ∧ acceleratedOrbit 15 32391 = 19460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32391) = 3 ^ 9 * m + 19460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32391.1, data_15_32391.2]

/-- Complete interval computation for depth 15, residue 32392. -/
theorem bounds_15_32392 : exactInterval 15 32392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32392 : oddCount 32392 15 = 6 ∧ acceleratedOrbit 15 32392 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32392) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32392.1, data_15_32392.2]

/-- Complete interval computation for depth 15, residue 32393. -/
theorem bounds_15_32393 : exactInterval 15 32393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32393 : oddCount 32393 15 = 9 ∧ acceleratedOrbit 15 32393 = 19459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32393) = 3 ^ 9 * m + 19459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32393.1, data_15_32393.2]

/-- Complete interval computation for depth 15, residue 32394. -/
theorem bounds_15_32394 : exactInterval 15 32394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32394 : oddCount 32394 15 = 6 ∧ acceleratedOrbit 15 32394 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32394) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32394.1, data_15_32394.2]

/-- Complete interval computation for depth 15, residue 32395. -/
theorem bounds_15_32395 : exactInterval 15 32395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32395 : oddCount 32395 15 = 6 ∧ acceleratedOrbit 15 32395 = 721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32395) = 3 ^ 6 * m + 721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32395.1, data_15_32395.2]

/-- Complete interval computation for depth 15, residue 32396. -/
theorem bounds_15_32396 : exactInterval 15 32396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32396 : oddCount 32396 15 = 6 ∧ acceleratedOrbit 15 32396 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32396) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32396.1, data_15_32396.2]

/-- Complete interval computation for depth 15, residue 32397. -/
theorem bounds_15_32397 : exactInterval 15 32397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32397 : oddCount 32397 15 = 6 ∧ acceleratedOrbit 15 32397 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32397) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32397.1, data_15_32397.2]

/-- Complete interval computation for depth 15, residue 32398. -/
theorem bounds_15_32398 : exactInterval 15 32398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32398 : oddCount 32398 15 = 8 ∧ acceleratedOrbit 15 32398 = 6488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32398) = 3 ^ 8 * m + 6488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32398.1, data_15_32398.2]

/-- Complete interval computation for depth 15, residue 32399. -/
theorem bounds_15_32399 : exactInterval 15 32399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32399 : oddCount 32399 15 = 8 ∧ acceleratedOrbit 15 32399 = 6488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32399) = 3 ^ 8 * m + 6488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32399.1, data_15_32399.2]

/-- Complete interval computation for depth 15, residue 32400. -/
theorem bounds_15_32400 : exactInterval 15 32400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32400 : oddCount 32400 15 = 8 ∧ acceleratedOrbit 15 32400 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32400) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32400.1, data_15_32400.2]

/-- Complete interval computation for depth 15, residue 32401. -/
theorem bounds_15_32401 : exactInterval 15 32401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32401 : oddCount 32401 15 = 6 ∧ acceleratedOrbit 15 32401 = 721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32401) = 3 ^ 6 * m + 721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32401.1, data_15_32401.2]

/-- Complete interval computation for depth 15, residue 32402. -/
theorem bounds_15_32402 : exactInterval 15 32402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32402 : oddCount 32402 15 = 6 ∧ acceleratedOrbit 15 32402 = 721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32402) = 3 ^ 6 * m + 721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32402.1, data_15_32402.2]

/-- Complete interval computation for depth 15, residue 32403. -/
theorem bounds_15_32403 : exactInterval 15 32403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32403 : oddCount 32403 15 = 6 ∧ acceleratedOrbit 15 32403 = 721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32403) = 3 ^ 6 * m + 721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32403.1, data_15_32403.2]

/-- Complete interval computation for depth 15, residue 32404. -/
theorem bounds_15_32404 : exactInterval 15 32404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32404 : oddCount 32404 15 = 8 ∧ acceleratedOrbit 15 32404 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32404) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32404.1, data_15_32404.2]

/-- Complete interval computation for depth 15, residue 32405. -/
theorem bounds_15_32405 : exactInterval 15 32405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32405 : oddCount 32405 15 = 8 ∧ acceleratedOrbit 15 32405 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32405) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32405.1, data_15_32405.2]

/-- Complete interval computation for depth 15, residue 32406. -/
theorem bounds_15_32406 : exactInterval 15 32406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32406 : oddCount 32406 15 = 6 ∧ acceleratedOrbit 15 32406 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32406) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32406.1, data_15_32406.2]

end Collatz.Research.PassageAtlas.Batch0989
