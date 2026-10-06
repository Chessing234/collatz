import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0025

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 368. -/
theorem bounds_10_368 : exactInterval 10 368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_368 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 368) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_368 : oddCount 368 10 = 3 ∧ acceleratedOrbit 10 368 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_368 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 368) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_368.1, data_10_368.2]

/-- Complete interval computation for depth 10, residue 369. -/
theorem bounds_10_369 : exactInterval 10 369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_369 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 369) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_369 : oddCount 369 10 = 3 ∧ acceleratedOrbit 10 369 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_369 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 369) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_369.1, data_10_369.2]

/-- Complete interval computation for depth 10, residue 370. -/
theorem bounds_10_370 : exactInterval 10 370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_370 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 370) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_370 : oddCount 370 10 = 5 ∧ acceleratedOrbit 10 370 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_370 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 370) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_370.1, data_10_370.2]

/-- Complete interval computation for depth 10, residue 371. -/
theorem bounds_10_371 : exactInterval 10 371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_371 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 371) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_371 : oddCount 371 10 = 5 ∧ acceleratedOrbit 10 371 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_371 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 371) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_371.1, data_10_371.2]

/-- Complete interval computation for depth 10, residue 372. -/
theorem bounds_10_372 : exactInterval 10 372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_372 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 372) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_372 : oddCount 372 10 = 3 ∧ acceleratedOrbit 10 372 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_372 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 372) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_372.1, data_10_372.2]

/-- Complete interval computation for depth 10, residue 373. -/
theorem bounds_10_373 : exactInterval 10 373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_373 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 373) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_373 : oddCount 373 10 = 3 ∧ acceleratedOrbit 10 373 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_373 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 373) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_373.1, data_10_373.2]

/-- Complete interval computation for depth 10, residue 374. -/
theorem bounds_10_374 : exactInterval 10 374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_374 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 374) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_374 : oddCount 374 10 = 6 ∧ acceleratedOrbit 10 374 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_374 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 374) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_374.1, data_10_374.2]

/-- Complete interval computation for depth 10, residue 375. -/
theorem bounds_10_375 : exactInterval 10 375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_375 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 375) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_375 : oddCount 375 10 = 6 ∧ acceleratedOrbit 10 375 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_375 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 375) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_375.1, data_10_375.2]

/-- Complete interval computation for depth 10, residue 376. -/
theorem bounds_10_376 : exactInterval 10 376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_376 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 376) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_376 : oddCount 376 10 = 5 ∧ acceleratedOrbit 10 376 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_376 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 376) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_376.1, data_10_376.2]

/-- Complete interval computation for depth 10, residue 377. -/
theorem bounds_10_377 : exactInterval 10 377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_377 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 377) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_377 : oddCount 377 10 = 8 ∧ acceleratedOrbit 10 377 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_377 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 377) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_377.1, data_10_377.2]

/-- Complete interval computation for depth 10, residue 378. -/
theorem bounds_10_378 : exactInterval 10 378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_378 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 378) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_378 : oddCount 378 10 = 5 ∧ acceleratedOrbit 10 378 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_378 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 378) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_378.1, data_10_378.2]

/-- Complete interval computation for depth 10, residue 379. -/
theorem bounds_10_379 : exactInterval 10 379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_379 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 379) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_379 : oddCount 379 10 = 6 ∧ acceleratedOrbit 10 379 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_379 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 379) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_379.1, data_10_379.2]

/-- Complete interval computation for depth 10, residue 380. -/
theorem bounds_10_380 : exactInterval 10 380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_380 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 380) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_380 : oddCount 380 10 = 5 ∧ acceleratedOrbit 10 380 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_380 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 380) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_380.1, data_10_380.2]

/-- Complete interval computation for depth 10, residue 381. -/
theorem bounds_10_381 : exactInterval 10 381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_381 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 381) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_381 : oddCount 381 10 = 5 ∧ acceleratedOrbit 10 381 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_381 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 381) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_381.1, data_10_381.2]

/-- Complete interval computation for depth 10, residue 382. -/
theorem bounds_10_382 : exactInterval 10 382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_382 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 382) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_382 : oddCount 382 10 = 7 ∧ acceleratedOrbit 10 382 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_382 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 382) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_382.1, data_10_382.2]

/-- Complete interval computation for depth 10, residue 383. -/
theorem bounds_10_383 : exactInterval 10 383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_383 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 383) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_383 : oddCount 383 10 = 7 ∧ acceleratedOrbit 10 383 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_383 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 383) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_383.1, data_10_383.2]

end Collatz.Research.StoppingAtlas.Batch0025
