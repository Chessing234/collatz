import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0222

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 322. -/
theorem bounds_12_322 : exactInterval 12 322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_322 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 322) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_322 : oddCount 322 12 = 7 ∧ acceleratedOrbit 12 322 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_322 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 322) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_322.1, data_12_322.2]

/-- Complete interval computation for depth 12, residue 323. -/
theorem bounds_12_323 : exactInterval 12 323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_323 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 323) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_323 : oddCount 323 12 = 7 ∧ acceleratedOrbit 12 323 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_323 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 323) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_323.1, data_12_323.2]

/-- Complete interval computation for depth 12, residue 324. -/
theorem bounds_12_324 : exactInterval 12 324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_324 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 324) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_324 : oddCount 324 12 = 5 ∧ acceleratedOrbit 12 324 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_324 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 324) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_324.1, data_12_324.2]

/-- Complete interval computation for depth 12, residue 325. -/
theorem bounds_12_325 : exactInterval 12 325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_325 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 325) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_325 : oddCount 325 12 = 5 ∧ acceleratedOrbit 12 325 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_325 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 325) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_325.1, data_12_325.2]

/-- Complete interval computation for depth 12, residue 326. -/
theorem bounds_12_326 : exactInterval 12 326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_326 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 326) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_326 : oddCount 326 12 = 5 ∧ acceleratedOrbit 12 326 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_326 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 326) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_326.1, data_12_326.2]

/-- Complete interval computation for depth 12, residue 327. -/
theorem bounds_12_327 : exactInterval 12 327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_327 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 327) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_327 : oddCount 327 12 = 9 ∧ acceleratedOrbit 12 327 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_327 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 327) = 3 ^ 9 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_327.1, data_12_327.2]

/-- Complete interval computation for depth 12, residue 328. -/
theorem bounds_12_328 : exactInterval 12 328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_328 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 328) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_328 : oddCount 328 12 = 7 ∧ acceleratedOrbit 12 328 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_328 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 328) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_328.1, data_12_328.2]

/-- Complete interval computation for depth 12, residue 329. -/
theorem bounds_12_329 : exactInterval 12 329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_329 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 329) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_329 : oddCount 329 12 = 6 ∧ acceleratedOrbit 12 329 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_329 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 329) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_329.1, data_12_329.2]

/-- Complete interval computation for depth 12, residue 330. -/
theorem bounds_12_330 : exactInterval 12 330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_330 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 330) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_330 : oddCount 330 12 = 7 ∧ acceleratedOrbit 12 330 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_330 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 330) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_330.1, data_12_330.2]

/-- Complete interval computation for depth 12, residue 331. -/
theorem bounds_12_331 : exactInterval 12 331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_331 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 331) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_331 : oddCount 331 12 = 5 ∧ acceleratedOrbit 12 331 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_331 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 331) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_331.1, data_12_331.2]

/-- Complete interval computation for depth 12, residue 332. -/
theorem bounds_12_332 : exactInterval 12 332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_332 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 332) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_332 : oddCount 332 12 = 7 ∧ acceleratedOrbit 12 332 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_332 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 332) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_332.1, data_12_332.2]

/-- Complete interval computation for depth 12, residue 333. -/
theorem bounds_12_333 : exactInterval 12 333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_333 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 333) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_333 : oddCount 333 12 = 7 ∧ acceleratedOrbit 12 333 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_333 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 333) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_333.1, data_12_333.2]

/-- Complete interval computation for depth 12, residue 334. -/
theorem bounds_12_334 : exactInterval 12 334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_334 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 334) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_334 : oddCount 334 12 = 9 ∧ acceleratedOrbit 12 334 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_334 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 334) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_334.1, data_12_334.2]

/-- Complete interval computation for depth 12, residue 335. -/
theorem bounds_12_335 : exactInterval 12 335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_335 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 335) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_335 : oddCount 335 12 = 9 ∧ acceleratedOrbit 12 335 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_335 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 335) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_335.1, data_12_335.2]

/-- Complete interval computation for depth 12, residue 336. -/
theorem bounds_12_336 : exactInterval 12 336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_336 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 336) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_336 : oddCount 336 12 = 2 ∧ acceleratedOrbit 12 336 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_336 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 336) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_336.1, data_12_336.2]

end Collatz.Research.StoppingAtlas.Batch0222
