import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch084

/-- Complete interval computation for depth 9, residue 338. -/
theorem bounds_9_338 : exactInterval 9 338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_338 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 338) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_338 : oddCount 338 9 = 7 ∧ acceleratedOrbit 9 338 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_338 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 338) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_338.1, data_9_338.2]

/-- Complete interval computation for depth 9, residue 339. -/
theorem bounds_9_339 : exactInterval 9 339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_339 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 339) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_339 : oddCount 339 9 = 7 ∧ acceleratedOrbit 9 339 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_339 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 339) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_339.1, data_9_339.2]

/-- Complete interval computation for depth 9, residue 340. -/
theorem bounds_9_340 : exactInterval 9 340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_340 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 340) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_340 : oddCount 340 9 = 1 ∧ acceleratedOrbit 9 340 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_340 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 340) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_340.1, data_9_340.2]

/-- Complete interval computation for depth 9, residue 341. -/
theorem bounds_9_341 : exactInterval 9 341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_341 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 341) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_341 : oddCount 341 9 = 1 ∧ acceleratedOrbit 9 341 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_341 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 341) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_341.1, data_9_341.2]

/-- Complete interval computation for depth 9, residue 342. -/
theorem bounds_9_342 : exactInterval 9 342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_342 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 342) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_342 : oddCount 342 9 = 5 ∧ acceleratedOrbit 9 342 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_342 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 342) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_342.1, data_9_342.2]

/-- Complete interval computation for depth 9, residue 343. -/
theorem bounds_9_343 : exactInterval 9 343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_343 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 343) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_343 : oddCount 343 9 = 5 ∧ acceleratedOrbit 9 343 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_343 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 343) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_343.1, data_9_343.2]

/-- Complete interval computation for depth 9, residue 344. -/
theorem bounds_9_344 : exactInterval 9 344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_344 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 344) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_344 : oddCount 344 9 = 4 ∧ acceleratedOrbit 9 344 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_344 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 344) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_344.1, data_9_344.2]

/-- Complete interval computation for depth 9, residue 345. -/
theorem bounds_9_345 : exactInterval 9 345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_345 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 345) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_345 : oddCount 345 9 = 4 ∧ acceleratedOrbit 9 345 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_345 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 345) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_345.1, data_9_345.2]

/-- Complete interval computation for depth 9, residue 346. -/
theorem bounds_9_346 : exactInterval 9 346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_346 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 346) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_346 : oddCount 346 9 = 4 ∧ acceleratedOrbit 9 346 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_346 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 346) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_346.1, data_9_346.2]

/-- Complete interval computation for depth 9, residue 347. -/
theorem bounds_9_347 : exactInterval 9 347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_347 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 347) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_347 : oddCount 347 9 = 6 ∧ acceleratedOrbit 9 347 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_347 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 347) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_347.1, data_9_347.2]

end Collatz.Research.DescentIntervals.Batch084
