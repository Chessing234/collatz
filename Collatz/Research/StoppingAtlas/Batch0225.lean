import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0225

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 368. -/
theorem bounds_12_368 : exactInterval 12 368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_368 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 368) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_368 : oddCount 368 12 = 4 ∧ acceleratedOrbit 12 368 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_368 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 368) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_368.1, data_12_368.2]

/-- Complete interval computation for depth 12, residue 369. -/
theorem bounds_12_369 : exactInterval 12 369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_369 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 369) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_369 : oddCount 369 12 = 4 ∧ acceleratedOrbit 12 369 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_369 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 369) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_369.1, data_12_369.2]

/-- Complete interval computation for depth 12, residue 370. -/
theorem bounds_12_370 : exactInterval 12 370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_370 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 370) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_370 : oddCount 370 12 = 6 ∧ acceleratedOrbit 12 370 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_370 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 370) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_370.1, data_12_370.2]

/-- Complete interval computation for depth 12, residue 371. -/
theorem bounds_12_371 : exactInterval 12 371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_371 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 371) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_371 : oddCount 371 12 = 6 ∧ acceleratedOrbit 12 371 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_371 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 371) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_371.1, data_12_371.2]

/-- Complete interval computation for depth 12, residue 372. -/
theorem bounds_12_372 : exactInterval 12 372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_372 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 372) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_372 : oddCount 372 12 = 4 ∧ acceleratedOrbit 12 372 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_372 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 372) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_372.1, data_12_372.2]

/-- Complete interval computation for depth 12, residue 373. -/
theorem bounds_12_373 : exactInterval 12 373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_373 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 373) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_373 : oddCount 373 12 = 4 ∧ acceleratedOrbit 12 373 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_373 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 373) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_373.1, data_12_373.2]

/-- Complete interval computation for depth 12, residue 374. -/
theorem bounds_12_374 : exactInterval 12 374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_374 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 374) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_374 : oddCount 374 12 = 7 ∧ acceleratedOrbit 12 374 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_374 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 374) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_374.1, data_12_374.2]

/-- Complete interval computation for depth 12, residue 375. -/
theorem bounds_12_375 : exactInterval 12 375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_375 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 375) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_375 : oddCount 375 12 = 7 ∧ acceleratedOrbit 12 375 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_375 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 375) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_375.1, data_12_375.2]

/-- Complete interval computation for depth 12, residue 376. -/
theorem bounds_12_376 : exactInterval 12 376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_376 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 376) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_376 : oddCount 376 12 = 7 ∧ acceleratedOrbit 12 376 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_376 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 376) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_376.1, data_12_376.2]

/-- Complete interval computation for depth 12, residue 377. -/
theorem bounds_12_377 : exactInterval 12 377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_377 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 377) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_377 : oddCount 377 12 = 9 ∧ acceleratedOrbit 12 377 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_377 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 377) = 3 ^ 9 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_377.1, data_12_377.2]

/-- Complete interval computation for depth 12, residue 378. -/
theorem bounds_12_378 : exactInterval 12 378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_378 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 378) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_378 : oddCount 378 12 = 7 ∧ acceleratedOrbit 12 378 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_378 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 378) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_378.1, data_12_378.2]

/-- Complete interval computation for depth 12, residue 379. -/
theorem bounds_12_379 : exactInterval 12 379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_379 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 379) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_379 : oddCount 379 12 = 8 ∧ acceleratedOrbit 12 379 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_379 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 379) = 3 ^ 8 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_379.1, data_12_379.2]

/-- Complete interval computation for depth 12, residue 380. -/
theorem bounds_12_380 : exactInterval 12 380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_380 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 380) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_380 : oddCount 380 12 = 7 ∧ acceleratedOrbit 12 380 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_380 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 380) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_380.1, data_12_380.2]

/-- Complete interval computation for depth 12, residue 381. -/
theorem bounds_12_381 : exactInterval 12 381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_381 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 381) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_381 : oddCount 381 12 = 7 ∧ acceleratedOrbit 12 381 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_381 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 381) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_381.1, data_12_381.2]

/-- Complete interval computation for depth 12, residue 382. -/
theorem bounds_12_382 : exactInterval 12 382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_382 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 382) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_382 : oddCount 382 12 = 7 ∧ acceleratedOrbit 12 382 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_382 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 382) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_382.1, data_12_382.2]

/-- Complete interval computation for depth 12, residue 383. -/
theorem bounds_12_383 : exactInterval 12 383 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_383 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 383) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_383 : oddCount 383 12 = 7 ∧ acceleratedOrbit 12 383 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_383 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 383) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_383.1, data_12_383.2]

end Collatz.Research.StoppingAtlas.Batch0225
