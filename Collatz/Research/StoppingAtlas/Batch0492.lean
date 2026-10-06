import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0492

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 373. -/
theorem bounds_13_373 : exactInterval 13 373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_373 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 373) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_373 : oddCount 373 13 = 4 ∧ acceleratedOrbit 13 373 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_373 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 373) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_373.1, data_13_373.2]

/-- Complete interval computation for depth 13, residue 374. -/
theorem bounds_13_374 : exactInterval 13 374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_374 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 374) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_374 : oddCount 374 13 = 7 ∧ acceleratedOrbit 13 374 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_374 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 374) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_374.1, data_13_374.2]

/-- Complete interval computation for depth 13, residue 375. -/
theorem bounds_13_375 : exactInterval 13 375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_375 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 375) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_375 : oddCount 375 13 = 7 ∧ acceleratedOrbit 13 375 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_375 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 375) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_375.1, data_13_375.2]

/-- Complete interval computation for depth 13, residue 376. -/
theorem bounds_13_376 : exactInterval 13 376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_376 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 376) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_376 : oddCount 376 13 = 7 ∧ acceleratedOrbit 13 376 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_376 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 376) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_376.1, data_13_376.2]

/-- Complete interval computation for depth 13, residue 377. -/
theorem bounds_13_377 : exactInterval 13 377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_377 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 377) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_377 : oddCount 377 13 = 9 ∧ acceleratedOrbit 13 377 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_377 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 377) = 3 ^ 9 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_377.1, data_13_377.2]

/-- Complete interval computation for depth 13, residue 378. -/
theorem bounds_13_378 : exactInterval 13 378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_378 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 378) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_378 : oddCount 378 13 = 7 ∧ acceleratedOrbit 13 378 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_378 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 378) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_378.1, data_13_378.2]

/-- Complete interval computation for depth 13, residue 379. -/
theorem bounds_13_379 : exactInterval 13 379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_379 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 379) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_379 : oddCount 379 13 = 9 ∧ acceleratedOrbit 13 379 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_379 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 379) = 3 ^ 9 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_379.1, data_13_379.2]

/-- Complete interval computation for depth 13, residue 380. -/
theorem bounds_13_380 : exactInterval 13 380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_380 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 380) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_380 : oddCount 380 13 = 7 ∧ acceleratedOrbit 13 380 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_380 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 380) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_380.1, data_13_380.2]

/-- Complete interval computation for depth 13, residue 381. -/
theorem bounds_13_381 : exactInterval 13 381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_381 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 381) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_381 : oddCount 381 13 = 7 ∧ acceleratedOrbit 13 381 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_381 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 381) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_381.1, data_13_381.2]

/-- Complete interval computation for depth 13, residue 382. -/
theorem bounds_13_382 : exactInterval 13 382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_382 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 382) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_382 : oddCount 382 13 = 8 ∧ acceleratedOrbit 13 382 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_382 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 382) = 3 ^ 8 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_382.1, data_13_382.2]

/-- Complete interval computation for depth 13, residue 383. -/
theorem bounds_13_383 : exactInterval 13 383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_383 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 383) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_383 : oddCount 383 13 = 8 ∧ acceleratedOrbit 13 383 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_383 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 383) = 3 ^ 8 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_383.1, data_13_383.2]

/-- Complete interval computation for depth 13, residue 384. -/
theorem bounds_13_384 : exactInterval 13 384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_384 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 384) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_384 : oddCount 384 13 = 3 ∧ acceleratedOrbit 13 384 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_384 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 384) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_384.1, data_13_384.2]

/-- Complete interval computation for depth 13, residue 385. -/
theorem bounds_13_385 : exactInterval 13 385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_385 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 385) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_385 : oddCount 385 13 = 6 ∧ acceleratedOrbit 13 385 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_385 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 385) = 3 ^ 6 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_385.1, data_13_385.2]

/-- Complete interval computation for depth 13, residue 386. -/
theorem bounds_13_386 : exactInterval 13 386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_386 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 386) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_386 : oddCount 386 13 = 7 ∧ acceleratedOrbit 13 386 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_386 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 386) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_386.1, data_13_386.2]

/-- Complete interval computation for depth 13, residue 387. -/
theorem bounds_13_387 : exactInterval 13 387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_387 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 387) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_387 : oddCount 387 13 = 7 ∧ acceleratedOrbit 13 387 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_387 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 387) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_387.1, data_13_387.2]

/-- Complete interval computation for depth 13, residue 388. -/
theorem bounds_13_388 : exactInterval 13 388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_388 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 388) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_388 : oddCount 388 13 = 7 ∧ acceleratedOrbit 13 388 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_388 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 388) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_388.1, data_13_388.2]

end Collatz.Research.StoppingAtlas.Batch0492
