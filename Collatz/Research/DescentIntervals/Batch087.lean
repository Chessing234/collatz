import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch087

/-- Complete interval computation for depth 9, residue 368. -/
theorem bounds_9_368 : exactInterval 9 368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_368 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 368) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_368 : oddCount 368 9 = 3 ∧ acceleratedOrbit 9 368 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_368 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 368) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_368.1, data_9_368.2]

/-- Complete interval computation for depth 9, residue 369. -/
theorem bounds_9_369 : exactInterval 9 369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_369 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 369) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_369 : oddCount 369 9 = 3 ∧ acceleratedOrbit 9 369 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_369 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 369) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_369.1, data_9_369.2]

/-- Complete interval computation for depth 9, residue 370. -/
theorem bounds_9_370 : exactInterval 9 370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_370 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 370) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_370 : oddCount 370 9 = 4 ∧ acceleratedOrbit 9 370 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_370 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 370) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_370.1, data_9_370.2]

/-- Complete interval computation for depth 9, residue 371. -/
theorem bounds_9_371 : exactInterval 9 371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_371 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 371) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_371 : oddCount 371 9 = 4 ∧ acceleratedOrbit 9 371 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_371 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 371) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_371.1, data_9_371.2]

/-- Complete interval computation for depth 9, residue 372. -/
theorem bounds_9_372 : exactInterval 9 372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_372 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 372) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_372 : oddCount 372 9 = 3 ∧ acceleratedOrbit 9 372 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_372 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 372) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_372.1, data_9_372.2]

/-- Complete interval computation for depth 9, residue 373. -/
theorem bounds_9_373 : exactInterval 9 373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_373 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 373) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_373 : oddCount 373 9 = 3 ∧ acceleratedOrbit 9 373 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_373 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 373) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_373.1, data_9_373.2]

/-- Complete interval computation for depth 9, residue 374. -/
theorem bounds_9_374 : exactInterval 9 374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_374 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 374) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_374 : oddCount 374 9 = 5 ∧ acceleratedOrbit 9 374 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_374 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 374) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_374.1, data_9_374.2]

/-- Complete interval computation for depth 9, residue 375. -/
theorem bounds_9_375 : exactInterval 9 375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_375 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 375) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_375 : oddCount 375 9 = 5 ∧ acceleratedOrbit 9 375 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_375 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 375) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_375.1, data_9_375.2]

/-- Complete interval computation for depth 9, residue 376. -/
theorem bounds_9_376 : exactInterval 9 376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_376 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 376) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_376 : oddCount 376 9 = 5 ∧ acceleratedOrbit 9 376 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_376 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 376) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_376.1, data_9_376.2]

/-- Complete interval computation for depth 9, residue 377. -/
theorem bounds_9_377 : exactInterval 9 377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_377 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 377) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_377 : oddCount 377 9 = 7 ∧ acceleratedOrbit 9 377 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_377 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 377) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_377.1, data_9_377.2]

/-- Complete interval computation for depth 9, residue 378. -/
theorem bounds_9_378 : exactInterval 9 378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_378 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 378) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_378 : oddCount 378 9 = 5 ∧ acceleratedOrbit 9 378 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_378 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 378) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_378.1, data_9_378.2]

end Collatz.Research.DescentIntervals.Batch087
