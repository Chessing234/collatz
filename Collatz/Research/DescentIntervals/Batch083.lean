import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch083

/-- Complete interval computation for depth 9, residue 328. -/
theorem bounds_9_328 : exactInterval 9 328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_328 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 328) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_328 : oddCount 328 9 = 5 ∧ acceleratedOrbit 9 328 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_328 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 328) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_328.1, data_9_328.2]

/-- Complete interval computation for depth 9, residue 329. -/
theorem bounds_9_329 : exactInterval 9 329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_329 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 329) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_329 : oddCount 329 9 = 5 ∧ acceleratedOrbit 9 329 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_329 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 329) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_329.1, data_9_329.2]

/-- Complete interval computation for depth 9, residue 330. -/
theorem bounds_9_330 : exactInterval 9 330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_330 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 330) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_330 : oddCount 330 9 = 5 ∧ acceleratedOrbit 9 330 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_330 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 330) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_330.1, data_9_330.2]

/-- Complete interval computation for depth 9, residue 331. -/
theorem bounds_9_331 : exactInterval 9 331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_331 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 331) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_331 : oddCount 331 9 = 4 ∧ acceleratedOrbit 9 331 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_331 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 331) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_331.1, data_9_331.2]

/-- Complete interval computation for depth 9, residue 332. -/
theorem bounds_9_332 : exactInterval 9 332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_332 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 332) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_332 : oddCount 332 9 = 5 ∧ acceleratedOrbit 9 332 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_332 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 332) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_332.1, data_9_332.2]

/-- Complete interval computation for depth 9, residue 333. -/
theorem bounds_9_333 : exactInterval 9 333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_333 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 333) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_333 : oddCount 333 9 = 5 ∧ acceleratedOrbit 9 333 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_333 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 333) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_333.1, data_9_333.2]

/-- Complete interval computation for depth 9, residue 334. -/
theorem bounds_9_334 : exactInterval 9 334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_334 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 334) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_334 : oddCount 334 9 = 6 ∧ acceleratedOrbit 9 334 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_334 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 334) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_334.1, data_9_334.2]

/-- Complete interval computation for depth 9, residue 335. -/
theorem bounds_9_335 : exactInterval 9 335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_335 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 335) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_335 : oddCount 335 9 = 6 ∧ acceleratedOrbit 9 335 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_335 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 335) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_335.1, data_9_335.2]

/-- Complete interval computation for depth 9, residue 336. -/
theorem bounds_9_336 : exactInterval 9 336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_336 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 336) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_336 : oddCount 336 9 = 1 ∧ acceleratedOrbit 9 336 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_336 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 336) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_336.1, data_9_336.2]

/-- Complete interval computation for depth 9, residue 337. -/
theorem bounds_9_337 : exactInterval 9 337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_337 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 337) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_337 : oddCount 337 9 = 6 ∧ acceleratedOrbit 9 337 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_337 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 337) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_337.1, data_9_337.2]

end Collatz.Research.DescentIntervals.Batch083
