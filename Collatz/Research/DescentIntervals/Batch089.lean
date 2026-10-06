import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch089

/-- Complete interval computation for depth 9, residue 389. -/
theorem bounds_9_389 : exactInterval 9 389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_389 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 389) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_389 : oddCount 389 9 = 5 ∧ acceleratedOrbit 9 389 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_389 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 389) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_389.1, data_9_389.2]

/-- Complete interval computation for depth 9, residue 390. -/
theorem bounds_9_390 : exactInterval 9 390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_390 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 390) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_390 : oddCount 390 9 = 5 ∧ acceleratedOrbit 9 390 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_390 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 390) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_390.1, data_9_390.2]

/-- Complete interval computation for depth 9, residue 391. -/
theorem bounds_9_391 : exactInterval 9 391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_391 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 391) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_391 : oddCount 391 9 = 4 ∧ acceleratedOrbit 9 391 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_391 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 391) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_391.1, data_9_391.2]

/-- Complete interval computation for depth 9, residue 392. -/
theorem bounds_9_392 : exactInterval 9 392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_392 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 392) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_392 : oddCount 392 9 = 2 ∧ acceleratedOrbit 9 392 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_392 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 392) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_392.1, data_9_392.2]

/-- Complete interval computation for depth 9, residue 393. -/
theorem bounds_9_393 : exactInterval 9 393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_393 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 393) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_393 : oddCount 393 9 = 6 ∧ acceleratedOrbit 9 393 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_393 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 393) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_393.1, data_9_393.2]

/-- Complete interval computation for depth 9, residue 394. -/
theorem bounds_9_394 : exactInterval 9 394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_394 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 394) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_394 : oddCount 394 9 = 2 ∧ acceleratedOrbit 9 394 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_394 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 394) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_394.1, data_9_394.2]

/-- Complete interval computation for depth 9, residue 395. -/
theorem bounds_9_395 : exactInterval 9 395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_395 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 395) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_395 : oddCount 395 9 = 6 ∧ acceleratedOrbit 9 395 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_395 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 395) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_395.1, data_9_395.2]

/-- Complete interval computation for depth 9, residue 396. -/
theorem bounds_9_396 : exactInterval 9 396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_396 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 396) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_396 : oddCount 396 9 = 2 ∧ acceleratedOrbit 9 396 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_396 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 396) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_396.1, data_9_396.2]

/-- Complete interval computation for depth 9, residue 397. -/
theorem bounds_9_397 : exactInterval 9 397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_397 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 397) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_397 : oddCount 397 9 = 2 ∧ acceleratedOrbit 9 397 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_397 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 397) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_397.1, data_9_397.2]

/-- Complete interval computation for depth 9, residue 398. -/
theorem bounds_9_398 : exactInterval 9 398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_398 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 398) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_398 : oddCount 398 9 = 5 ∧ acceleratedOrbit 9 398 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_398 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 398) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_398.1, data_9_398.2]

end Collatz.Research.DescentIntervals.Batch089
