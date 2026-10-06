import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch082

/-- Complete interval computation for depth 9, residue 317. -/
theorem bounds_9_317 : exactInterval 9 317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_317 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 317) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_317 : oddCount 317 9 = 5 ∧ acceleratedOrbit 9 317 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_317 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 317) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_317.1, data_9_317.2]

/-- Complete interval computation for depth 9, residue 318. -/
theorem bounds_9_318 : exactInterval 9 318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_318 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 318) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_318 : oddCount 318 9 = 7 ∧ acceleratedOrbit 9 318 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_318 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 318) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_318.1, data_9_318.2]

/-- Complete interval computation for depth 9, residue 319. -/
theorem bounds_9_319 : exactInterval 9 319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_319 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 319) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_319 : oddCount 319 9 = 7 ∧ acceleratedOrbit 9 319 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_319 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 319) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_319.1, data_9_319.2]

/-- Complete interval computation for depth 9, residue 320. -/
theorem bounds_9_320 : exactInterval 9 320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_320 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 320) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_320 : oddCount 320 9 = 1 ∧ acceleratedOrbit 9 320 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_320 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 320) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_320.1, data_9_320.2]

/-- Complete interval computation for depth 9, residue 321. -/
theorem bounds_9_321 : exactInterval 9 321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_321 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 321) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_321 : oddCount 321 9 = 3 ∧ acceleratedOrbit 9 321 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_321 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 321) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_321.1, data_9_321.2]

/-- Complete interval computation for depth 9, residue 322. -/
theorem bounds_9_322 : exactInterval 9 322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_322 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 322) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_322 : oddCount 322 9 = 5 ∧ acceleratedOrbit 9 322 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_322 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 322) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_322.1, data_9_322.2]

/-- Complete interval computation for depth 9, residue 323. -/
theorem bounds_9_323 : exactInterval 9 323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_323 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 323) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_323 : oddCount 323 9 = 5 ∧ acceleratedOrbit 9 323 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_323 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 323) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_323.1, data_9_323.2]

/-- Complete interval computation for depth 9, residue 324. -/
theorem bounds_9_324 : exactInterval 9 324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_324 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 324) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_324 : oddCount 324 9 = 4 ∧ acceleratedOrbit 9 324 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_324 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 324) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_324.1, data_9_324.2]

/-- Complete interval computation for depth 9, residue 325. -/
theorem bounds_9_325 : exactInterval 9 325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_325 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 325) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_325 : oddCount 325 9 = 4 ∧ acceleratedOrbit 9 325 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_325 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 325) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_325.1, data_9_325.2]

/-- Complete interval computation for depth 9, residue 326. -/
theorem bounds_9_326 : exactInterval 9 326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_326 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 326) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_326 : oddCount 326 9 = 4 ∧ acceleratedOrbit 9 326 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_326 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 326) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_326.1, data_9_326.2]

/-- Complete interval computation for depth 9, residue 327. -/
theorem bounds_9_327 : exactInterval 9 327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_327 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 327) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_327 : oddCount 327 9 = 7 ∧ acceleratedOrbit 9 327 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_327 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 327) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_327.1, data_9_327.2]

end Collatz.Research.DescentIntervals.Batch082
