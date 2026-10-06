import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0022

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 322. -/
theorem bounds_10_322 : exactInterval 10 322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_322 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 322) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_322 : oddCount 322 10 = 6 ∧ acceleratedOrbit 10 322 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_322 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 322) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_322.1, data_10_322.2]

/-- Complete interval computation for depth 10, residue 323. -/
theorem bounds_10_323 : exactInterval 10 323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_323 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 323) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_323 : oddCount 323 10 = 6 ∧ acceleratedOrbit 10 323 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_323 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 323) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_323.1, data_10_323.2]

/-- Complete interval computation for depth 10, residue 324. -/
theorem bounds_10_324 : exactInterval 10 324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_324 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 324) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_324 : oddCount 324 10 = 5 ∧ acceleratedOrbit 10 324 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_324 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 324) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_324.1, data_10_324.2]

/-- Complete interval computation for depth 10, residue 325. -/
theorem bounds_10_325 : exactInterval 10 325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_325 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 325) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_325 : oddCount 325 10 = 5 ∧ acceleratedOrbit 10 325 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_325 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 325) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_325.1, data_10_325.2]

/-- Complete interval computation for depth 10, residue 326. -/
theorem bounds_10_326 : exactInterval 10 326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_326 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 326) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_326 : oddCount 326 10 = 5 ∧ acceleratedOrbit 10 326 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_326 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 326) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_326.1, data_10_326.2]

/-- Complete interval computation for depth 10, residue 327. -/
theorem bounds_10_327 : exactInterval 10 327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_327 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 327) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_327 : oddCount 327 10 = 8 ∧ acceleratedOrbit 10 327 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_327 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 327) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_327.1, data_10_327.2]

/-- Complete interval computation for depth 10, residue 328. -/
theorem bounds_10_328 : exactInterval 10 328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_328 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 328) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_328 : oddCount 328 10 = 6 ∧ acceleratedOrbit 10 328 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_328 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 328) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_328.1, data_10_328.2]

/-- Complete interval computation for depth 10, residue 329. -/
theorem bounds_10_329 : exactInterval 10 329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_329 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 329) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_329 : oddCount 329 10 = 6 ∧ acceleratedOrbit 10 329 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_329 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 329) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_329.1, data_10_329.2]

/-- Complete interval computation for depth 10, residue 330. -/
theorem bounds_10_330 : exactInterval 10 330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_330 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 330) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_330 : oddCount 330 10 = 6 ∧ acceleratedOrbit 10 330 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_330 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 330) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_330.1, data_10_330.2]

/-- Complete interval computation for depth 10, residue 331. -/
theorem bounds_10_331 : exactInterval 10 331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_331 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 331) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_331 : oddCount 331 10 = 5 ∧ acceleratedOrbit 10 331 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_331 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 331) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_331.1, data_10_331.2]

/-- Complete interval computation for depth 10, residue 332. -/
theorem bounds_10_332 : exactInterval 10 332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_332 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 332) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_332 : oddCount 332 10 = 6 ∧ acceleratedOrbit 10 332 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_332 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 332) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_332.1, data_10_332.2]

/-- Complete interval computation for depth 10, residue 333. -/
theorem bounds_10_333 : exactInterval 10 333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_333 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 333) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_333 : oddCount 333 10 = 6 ∧ acceleratedOrbit 10 333 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_333 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 333) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_333.1, data_10_333.2]

/-- Complete interval computation for depth 10, residue 334. -/
theorem bounds_10_334 : exactInterval 10 334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_334 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 334) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_334 : oddCount 334 10 = 7 ∧ acceleratedOrbit 10 334 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_334 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 334) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_334.1, data_10_334.2]

/-- Complete interval computation for depth 10, residue 335. -/
theorem bounds_10_335 : exactInterval 10 335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_335 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 335) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_335 : oddCount 335 10 = 7 ∧ acceleratedOrbit 10 335 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_335 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 335) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_335.1, data_10_335.2]

/-- Complete interval computation for depth 10, residue 336. -/
theorem bounds_10_336 : exactInterval 10 336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_336 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 336) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_336 : oddCount 336 10 = 1 ∧ acceleratedOrbit 10 336 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_336 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 336) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_336.1, data_10_336.2]

end Collatz.Research.StoppingAtlas.Batch0022
