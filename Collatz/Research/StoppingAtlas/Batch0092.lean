import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0092

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 373. -/
theorem bounds_11_373 : exactInterval 11 373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_373 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 373) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_373 : oddCount 373 11 = 3 ∧ acceleratedOrbit 11 373 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_373 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 373) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_373.1, data_11_373.2]

/-- Complete interval computation for depth 11, residue 374. -/
theorem bounds_11_374 : exactInterval 11 374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_374 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 374) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_374 : oddCount 374 11 = 7 ∧ acceleratedOrbit 11 374 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_374 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 374) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_374.1, data_11_374.2]

/-- Complete interval computation for depth 11, residue 375. -/
theorem bounds_11_375 : exactInterval 11 375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_375 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 375) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_375 : oddCount 375 11 = 7 ∧ acceleratedOrbit 11 375 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_375 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 375) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_375.1, data_11_375.2]

/-- Complete interval computation for depth 11, residue 376. -/
theorem bounds_11_376 : exactInterval 11 376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_376 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 376) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_376 : oddCount 376 11 = 6 ∧ acceleratedOrbit 11 376 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_376 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 376) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_376.1, data_11_376.2]

/-- Complete interval computation for depth 11, residue 377. -/
theorem bounds_11_377 : exactInterval 11 377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_377 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 377) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_377 : oddCount 377 11 = 9 ∧ acceleratedOrbit 11 377 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_377 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 377) = 3 ^ 9 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_377.1, data_11_377.2]

/-- Complete interval computation for depth 11, residue 378. -/
theorem bounds_11_378 : exactInterval 11 378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_378 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 378) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_378 : oddCount 378 11 = 6 ∧ acceleratedOrbit 11 378 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_378 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 378) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_378.1, data_11_378.2]

/-- Complete interval computation for depth 11, residue 379. -/
theorem bounds_11_379 : exactInterval 11 379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_379 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 379) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_379 : oddCount 379 11 = 7 ∧ acceleratedOrbit 11 379 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_379 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 379) = 3 ^ 7 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_379.1, data_11_379.2]

/-- Complete interval computation for depth 11, residue 380. -/
theorem bounds_11_380 : exactInterval 11 380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_380 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 380) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_380 : oddCount 380 11 = 6 ∧ acceleratedOrbit 11 380 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_380 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 380) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_380.1, data_11_380.2]

/-- Complete interval computation for depth 11, residue 381. -/
theorem bounds_11_381 : exactInterval 11 381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_381 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 381) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_381 : oddCount 381 11 = 6 ∧ acceleratedOrbit 11 381 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_381 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 381) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_381.1, data_11_381.2]

/-- Complete interval computation for depth 11, residue 382. -/
theorem bounds_11_382 : exactInterval 11 382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_382 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 382) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_382 : oddCount 382 11 = 7 ∧ acceleratedOrbit 11 382 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_382 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 382) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_382.1, data_11_382.2]

/-- Complete interval computation for depth 11, residue 383. -/
theorem bounds_11_383 : exactInterval 11 383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_383 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 383) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_383 : oddCount 383 11 = 7 ∧ acceleratedOrbit 11 383 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_383 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 383) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_383.1, data_11_383.2]

/-- Complete interval computation for depth 11, residue 384. -/
theorem bounds_11_384 : exactInterval 11 384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_384 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 384) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_384 : oddCount 384 11 = 2 ∧ acceleratedOrbit 11 384 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_384 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 384) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_384.1, data_11_384.2]

/-- Complete interval computation for depth 11, residue 385. -/
theorem bounds_11_385 : exactInterval 11 385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_385 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 385) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_385 : oddCount 385 11 = 5 ∧ acceleratedOrbit 11 385 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_385 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 385) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_385.1, data_11_385.2]

/-- Complete interval computation for depth 11, residue 386. -/
theorem bounds_11_386 : exactInterval 11 386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_386 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 386) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_386 : oddCount 386 11 = 5 ∧ acceleratedOrbit 11 386 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_386 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 386) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_386.1, data_11_386.2]

/-- Complete interval computation for depth 11, residue 387. -/
theorem bounds_11_387 : exactInterval 11 387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_387 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 387) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_387 : oddCount 387 11 = 5 ∧ acceleratedOrbit 11 387 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_387 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 387) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_387.1, data_11_387.2]

/-- Complete interval computation for depth 11, residue 388. -/
theorem bounds_11_388 : exactInterval 11 388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_388 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 388) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_388 : oddCount 388 11 = 5 ∧ acceleratedOrbit 11 388 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_388 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 388) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_388.1, data_11_388.2]

end Collatz.Research.StoppingAtlas.Batch0092
