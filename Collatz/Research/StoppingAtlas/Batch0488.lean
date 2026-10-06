import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0488

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 312. -/
theorem bounds_13_312 : exactInterval 13 312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_312 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 312) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_312 : oddCount 312 13 = 6 ∧ acceleratedOrbit 13 312 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_312 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 312) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_312.1, data_13_312.2]

/-- Complete interval computation for depth 13, residue 313. -/
theorem bounds_13_313 : exactInterval 13 313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_313 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 313) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_313 : oddCount 313 13 = 8 ∧ acceleratedOrbit 13 313 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_313 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 313) = 3 ^ 8 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_313.1, data_13_313.2]

/-- Complete interval computation for depth 13, residue 314. -/
theorem bounds_13_314 : exactInterval 13 314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_314 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 314) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_314 : oddCount 314 13 = 6 ∧ acceleratedOrbit 13 314 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_314 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 314) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_314.1, data_13_314.2]

/-- Complete interval computation for depth 13, residue 315. -/
theorem bounds_13_315 : exactInterval 13 315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_315 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 315) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_315 : oddCount 315 13 = 6 ∧ acceleratedOrbit 13 315 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_315 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 315) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_315.1, data_13_315.2]

/-- Complete interval computation for depth 13, residue 316. -/
theorem bounds_13_316 : exactInterval 13 316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_316 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 316) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_316 : oddCount 316 13 = 6 ∧ acceleratedOrbit 13 316 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_316 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 316) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_316.1, data_13_316.2]

/-- Complete interval computation for depth 13, residue 317. -/
theorem bounds_13_317 : exactInterval 13 317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_317 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 317) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_317 : oddCount 317 13 = 6 ∧ acceleratedOrbit 13 317 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_317 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 317) = 3 ^ 6 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_317.1, data_13_317.2]

/-- Complete interval computation for depth 13, residue 318. -/
theorem bounds_13_318 : exactInterval 13 318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_318 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 318) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_318 : oddCount 318 13 = 10 ∧ acceleratedOrbit 13 318 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_318 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 318) = 3 ^ 10 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_318.1, data_13_318.2]

/-- Complete interval computation for depth 13, residue 319. -/
theorem bounds_13_319 : exactInterval 13 319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_319 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 319) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_319 : oddCount 319 13 = 10 ∧ acceleratedOrbit 13 319 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_319 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 319) = 3 ^ 10 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_319.1, data_13_319.2]

/-- Complete interval computation for depth 13, residue 320. -/
theorem bounds_13_320 : exactInterval 13 320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_320 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 320) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_320 : oddCount 320 13 = 3 ∧ acceleratedOrbit 13 320 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_320 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 320) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_320.1, data_13_320.2]

/-- Complete interval computation for depth 13, residue 321. -/
theorem bounds_13_321 : exactInterval 13 321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_321 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 321) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_321 : oddCount 321 13 = 5 ∧ acceleratedOrbit 13 321 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_321 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 321) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_321.1, data_13_321.2]

/-- Complete interval computation for depth 13, residue 322. -/
theorem bounds_13_322 : exactInterval 13 322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_322 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 322) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_322 : oddCount 322 13 = 8 ∧ acceleratedOrbit 13 322 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_322 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 322) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_322.1, data_13_322.2]

/-- Complete interval computation for depth 13, residue 323. -/
theorem bounds_13_323 : exactInterval 13 323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_323 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 323) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_323 : oddCount 323 13 = 8 ∧ acceleratedOrbit 13 323 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_323 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 323) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_323.1, data_13_323.2]

/-- Complete interval computation for depth 13, residue 324. -/
theorem bounds_13_324 : exactInterval 13 324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_324 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 324) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_324 : oddCount 324 13 = 5 ∧ acceleratedOrbit 13 324 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_324 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 324) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_324.1, data_13_324.2]

/-- Complete interval computation for depth 13, residue 325. -/
theorem bounds_13_325 : exactInterval 13 325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_325 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 325) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_325 : oddCount 325 13 = 5 ∧ acceleratedOrbit 13 325 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_325 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 325) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_325.1, data_13_325.2]

/-- Complete interval computation for depth 13, residue 326. -/
theorem bounds_13_326 : exactInterval 13 326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_326 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 326) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_326 : oddCount 326 13 = 5 ∧ acceleratedOrbit 13 326 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_326 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 326) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_326.1, data_13_326.2]

end Collatz.Research.StoppingAtlas.Batch0488
