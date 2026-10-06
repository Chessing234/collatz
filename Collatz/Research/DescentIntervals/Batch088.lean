import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch088

/-- Complete interval computation for depth 9, residue 379. -/
theorem bounds_9_379 : exactInterval 9 379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_379 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 379) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_379 : oddCount 379 9 = 6 ∧ acceleratedOrbit 9 379 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_379 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 379) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_379.1, data_9_379.2]

/-- Complete interval computation for depth 9, residue 380. -/
theorem bounds_9_380 : exactInterval 9 380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_380 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 380) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_380 : oddCount 380 9 = 5 ∧ acceleratedOrbit 9 380 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_380 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 380) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_380.1, data_9_380.2]

/-- Complete interval computation for depth 9, residue 381. -/
theorem bounds_9_381 : exactInterval 9 381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_381 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 381) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_381 : oddCount 381 9 = 5 ∧ acceleratedOrbit 9 381 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_381 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 381) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_381.1, data_9_381.2]

/-- Complete interval computation for depth 9, residue 382. -/
theorem bounds_9_382 : exactInterval 9 382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_382 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 382) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_382 : oddCount 382 9 = 7 ∧ acceleratedOrbit 9 382 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_382 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 382) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_382.1, data_9_382.2]

/-- Complete interval computation for depth 9, residue 383. -/
theorem bounds_9_383 : exactInterval 9 383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_383 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 383) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_383 : oddCount 383 9 = 7 ∧ acceleratedOrbit 9 383 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_383 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 383) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_383.1, data_9_383.2]

/-- Complete interval computation for depth 9, residue 384. -/
theorem bounds_9_384 : exactInterval 9 384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_384 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 384) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_384 : oddCount 384 9 = 2 ∧ acceleratedOrbit 9 384 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_384 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 384) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_384.1, data_9_384.2]

/-- Complete interval computation for depth 9, residue 385. -/
theorem bounds_9_385 : exactInterval 9 385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_385 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 385) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_385 : oddCount 385 9 = 5 ∧ acceleratedOrbit 9 385 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_385 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 385) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_385.1, data_9_385.2]

/-- Complete interval computation for depth 9, residue 386. -/
theorem bounds_9_386 : exactInterval 9 386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_386 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 386) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_386 : oddCount 386 9 = 4 ∧ acceleratedOrbit 9 386 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_386 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 386) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_386.1, data_9_386.2]

/-- Complete interval computation for depth 9, residue 387. -/
theorem bounds_9_387 : exactInterval 9 387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_387 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 387) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_387 : oddCount 387 9 = 4 ∧ acceleratedOrbit 9 387 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_387 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 387) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_387.1, data_9_387.2]

/-- Complete interval computation for depth 9, residue 388. -/
theorem bounds_9_388 : exactInterval 9 388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_388 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 388) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_388 : oddCount 388 9 = 5 ∧ acceleratedOrbit 9 388 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_388 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 388) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_388.1, data_9_388.2]

end Collatz.Research.DescentIntervals.Batch088
