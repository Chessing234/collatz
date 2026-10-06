import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0867

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28377. -/
theorem bounds_15_28377 : exactInterval 15 28377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28377 : oddCount 28377 15 = 6 ∧ acceleratedOrbit 15 28377 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28377) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28377.1, data_15_28377.2]

/-- Complete interval computation for depth 15, residue 28378. -/
theorem bounds_15_28378 : exactInterval 15 28378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28378 : oddCount 28378 15 = 6 ∧ acceleratedOrbit 15 28378 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28378) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28378.1, data_15_28378.2]

/-- Complete interval computation for depth 15, residue 28379. -/
theorem bounds_15_28379 : exactInterval 15 28379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28379 : oddCount 28379 15 = 9 ∧ acceleratedOrbit 15 28379 = 17048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28379) = 3 ^ 9 * m + 17048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28379.1, data_15_28379.2]

/-- Complete interval computation for depth 15, residue 28380. -/
theorem bounds_15_28380 : exactInterval 15 28380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28380 : oddCount 28380 15 = 6 ∧ acceleratedOrbit 15 28380 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28380) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28380.1, data_15_28380.2]

/-- Complete interval computation for depth 15, residue 28381. -/
theorem bounds_15_28381 : exactInterval 15 28381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28381 : oddCount 28381 15 = 6 ∧ acceleratedOrbit 15 28381 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28381) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28381.1, data_15_28381.2]

/-- Complete interval computation for depth 15, residue 28382. -/
theorem bounds_15_28382 : exactInterval 15 28382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28382 : oddCount 28382 15 = 10 ∧ acceleratedOrbit 15 28382 = 51151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28382) = 3 ^ 10 * m + 51151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28382.1, data_15_28382.2]

/-- Complete interval computation for depth 15, residue 28383. -/
theorem bounds_15_28383 : exactInterval 15 28383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28383 : oddCount 28383 15 = 10 ∧ acceleratedOrbit 15 28383 = 51151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28383) = 3 ^ 10 * m + 51151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28383.1, data_15_28383.2]

/-- Complete interval computation for depth 15, residue 28384. -/
theorem bounds_15_28384 : exactInterval 15 28384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28384 : oddCount 28384 15 = 5 ∧ acceleratedOrbit 15 28384 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28384) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28384.1, data_15_28384.2]

/-- Complete interval computation for depth 15, residue 28385. -/
theorem bounds_15_28385 : exactInterval 15 28385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28385 : oddCount 28385 15 = 8 ∧ acceleratedOrbit 15 28385 = 5684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28385) = 3 ^ 8 * m + 5684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28385.1, data_15_28385.2]

/-- Complete interval computation for depth 15, residue 28386. -/
theorem bounds_15_28386 : exactInterval 15 28386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28386 : oddCount 28386 15 = 5 ∧ acceleratedOrbit 15 28386 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28386) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28386.1, data_15_28386.2]

/-- Complete interval computation for depth 15, residue 28387. -/
theorem bounds_15_28387 : exactInterval 15 28387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28387 : oddCount 28387 15 = 5 ∧ acceleratedOrbit 15 28387 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28387) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28387.1, data_15_28387.2]

/-- Complete interval computation for depth 15, residue 28388. -/
theorem bounds_15_28388 : exactInterval 15 28388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28388 : oddCount 28388 15 = 6 ∧ acceleratedOrbit 15 28388 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28388) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28388.1, data_15_28388.2]

/-- Complete interval computation for depth 15, residue 28389. -/
theorem bounds_15_28389 : exactInterval 15 28389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28389 : oddCount 28389 15 = 6 ∧ acceleratedOrbit 15 28389 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28389) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28389.1, data_15_28389.2]

/-- Complete interval computation for depth 15, residue 28390. -/
theorem bounds_15_28390 : exactInterval 15 28390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28390 : oddCount 28390 15 = 6 ∧ acceleratedOrbit 15 28390 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28390) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28390.1, data_15_28390.2]

/-- Complete interval computation for depth 15, residue 28391. -/
theorem bounds_15_28391 : exactInterval 15 28391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28391 : oddCount 28391 15 = 11 ∧ acceleratedOrbit 15 28391 = 153494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28391) = 3 ^ 11 * m + 153494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28391.1, data_15_28391.2]

/-- Complete interval computation for depth 15, residue 28392. -/
theorem bounds_15_28392 : exactInterval 15 28392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28392 : oddCount 28392 15 = 5 ∧ acceleratedOrbit 15 28392 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28392) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28392.1, data_15_28392.2]

/-- Complete interval computation for depth 15, residue 28393. -/
theorem bounds_15_28393 : exactInterval 15 28393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28393 : oddCount 28393 15 = 9 ∧ acceleratedOrbit 15 28393 = 17057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28393) = 3 ^ 9 * m + 17057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28393.1, data_15_28393.2]

/-- Complete interval computation for depth 15, residue 28394. -/
theorem bounds_15_28394 : exactInterval 15 28394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28394 : oddCount 28394 15 = 5 ∧ acceleratedOrbit 15 28394 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28394) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28394.1, data_15_28394.2]

/-- Complete interval computation for depth 15, residue 28395. -/
theorem bounds_15_28395 : exactInterval 15 28395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28395 : oddCount 28395 15 = 8 ∧ acceleratedOrbit 15 28395 = 5687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28395) = 3 ^ 8 * m + 5687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28395.1, data_15_28395.2]

/-- Complete interval computation for depth 15, residue 28396. -/
theorem bounds_15_28396 : exactInterval 15 28396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28396 : oddCount 28396 15 = 6 ∧ acceleratedOrbit 15 28396 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28396) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28396.1, data_15_28396.2]

/-- Complete interval computation for depth 15, residue 28397. -/
theorem bounds_15_28397 : exactInterval 15 28397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28397 : oddCount 28397 15 = 6 ∧ acceleratedOrbit 15 28397 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28397) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28397.1, data_15_28397.2]

/-- Complete interval computation for depth 15, residue 28398. -/
theorem bounds_15_28398 : exactInterval 15 28398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28398 : oddCount 28398 15 = 6 ∧ acceleratedOrbit 15 28398 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28398) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28398.1, data_15_28398.2]

/-- Complete interval computation for depth 15, residue 28399. -/
theorem bounds_15_28399 : exactInterval 15 28399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28399 : oddCount 28399 15 = 11 ∧ acceleratedOrbit 15 28399 = 153535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28399) = 3 ^ 11 * m + 153535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28399.1, data_15_28399.2]

/-- Complete interval computation for depth 15, residue 28400. -/
theorem bounds_15_28400 : exactInterval 15 28400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28400 : oddCount 28400 15 = 8 ∧ acceleratedOrbit 15 28400 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28400) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28400.1, data_15_28400.2]

/-- Complete interval computation for depth 15, residue 28401. -/
theorem bounds_15_28401 : exactInterval 15 28401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28401 : oddCount 28401 15 = 5 ∧ acceleratedOrbit 15 28401 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28401) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28401.1, data_15_28401.2]

/-- Complete interval computation for depth 15, residue 28402. -/
theorem bounds_15_28402 : exactInterval 15 28402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28402 : oddCount 28402 15 = 10 ∧ acceleratedOrbit 15 28402 = 51191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28402) = 3 ^ 10 * m + 51191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28402.1, data_15_28402.2]

/-- Complete interval computation for depth 15, residue 28403. -/
theorem bounds_15_28403 : exactInterval 15 28403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28403 : oddCount 28403 15 = 10 ∧ acceleratedOrbit 15 28403 = 51191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28403) = 3 ^ 10 * m + 51191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28403.1, data_15_28403.2]

/-- Complete interval computation for depth 15, residue 28404. -/
theorem bounds_15_28404 : exactInterval 15 28404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28404 : oddCount 28404 15 = 8 ∧ acceleratedOrbit 15 28404 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28404) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28404.1, data_15_28404.2]

/-- Complete interval computation for depth 15, residue 28405. -/
theorem bounds_15_28405 : exactInterval 15 28405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28405 : oddCount 28405 15 = 8 ∧ acceleratedOrbit 15 28405 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28405) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28405.1, data_15_28405.2]

/-- Complete interval computation for depth 15, residue 28406. -/
theorem bounds_15_28406 : exactInterval 15 28406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28406 : oddCount 28406 15 = 9 ∧ acceleratedOrbit 15 28406 = 17066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28406) = 3 ^ 9 * m + 17066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28406.1, data_15_28406.2]

/-- Complete interval computation for depth 15, residue 28407. -/
theorem bounds_15_28407 : exactInterval 15 28407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28407 : oddCount 28407 15 = 9 ∧ acceleratedOrbit 15 28407 = 17066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28407) = 3 ^ 9 * m + 17066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28407.1, data_15_28407.2]

/-- Complete interval computation for depth 15, residue 28408. -/
theorem bounds_15_28408 : exactInterval 15 28408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28408 : oddCount 28408 15 = 8 ∧ acceleratedOrbit 15 28408 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28408) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28408.1, data_15_28408.2]

end Collatz.Research.PassageAtlas.Batch0867
