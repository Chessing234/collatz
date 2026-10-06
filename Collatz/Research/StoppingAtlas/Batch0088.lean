import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0088

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 312. -/
theorem bounds_11_312 : exactInterval 11 312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_312 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 312) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_312 : oddCount 312 11 = 5 ∧ acceleratedOrbit 11 312 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_312 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 312) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_312.1, data_11_312.2]

/-- Complete interval computation for depth 11, residue 313. -/
theorem bounds_11_313 : exactInterval 11 313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_313 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 313) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_313 : oddCount 313 11 = 7 ∧ acceleratedOrbit 11 313 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_313 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 313) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_313.1, data_11_313.2]

/-- Complete interval computation for depth 11, residue 314. -/
theorem bounds_11_314 : exactInterval 11 314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_314 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 314) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_314 : oddCount 314 11 = 5 ∧ acceleratedOrbit 11 314 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_314 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 314) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_314.1, data_11_314.2]

/-- Complete interval computation for depth 11, residue 315. -/
theorem bounds_11_315 : exactInterval 11 315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_315 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 315) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_315 : oddCount 315 11 = 5 ∧ acceleratedOrbit 11 315 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_315 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 315) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_315.1, data_11_315.2]

/-- Complete interval computation for depth 11, residue 316. -/
theorem bounds_11_316 : exactInterval 11 316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_316 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 316) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_316 : oddCount 316 11 = 5 ∧ acceleratedOrbit 11 316 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_316 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 316) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_316.1, data_11_316.2]

/-- Complete interval computation for depth 11, residue 317. -/
theorem bounds_11_317 : exactInterval 11 317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_317 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 317) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_317 : oddCount 317 11 = 5 ∧ acceleratedOrbit 11 317 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_317 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 317) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_317.1, data_11_317.2]

/-- Complete interval computation for depth 11, residue 318. -/
theorem bounds_11_318 : exactInterval 11 318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_318 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 318) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_318 : oddCount 318 11 = 9 ∧ acceleratedOrbit 11 318 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_318 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 318) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_318.1, data_11_318.2]

/-- Complete interval computation for depth 11, residue 319. -/
theorem bounds_11_319 : exactInterval 11 319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_319 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 319) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_319 : oddCount 319 11 = 9 ∧ acceleratedOrbit 11 319 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_319 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 319) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_319.1, data_11_319.2]

/-- Complete interval computation for depth 11, residue 320. -/
theorem bounds_11_320 : exactInterval 11 320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_320 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 320) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_320 : oddCount 320 11 = 2 ∧ acceleratedOrbit 11 320 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_320 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 320) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_320.1, data_11_320.2]

/-- Complete interval computation for depth 11, residue 321. -/
theorem bounds_11_321 : exactInterval 11 321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_321 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 321) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_321 : oddCount 321 11 = 4 ∧ acceleratedOrbit 11 321 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_321 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 321) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_321.1, data_11_321.2]

/-- Complete interval computation for depth 11, residue 322. -/
theorem bounds_11_322 : exactInterval 11 322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_322 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 322) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_322 : oddCount 322 11 = 7 ∧ acceleratedOrbit 11 322 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_322 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 322) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_322.1, data_11_322.2]

/-- Complete interval computation for depth 11, residue 323. -/
theorem bounds_11_323 : exactInterval 11 323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_323 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 323) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_323 : oddCount 323 11 = 7 ∧ acceleratedOrbit 11 323 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_323 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 323) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_323.1, data_11_323.2]

/-- Complete interval computation for depth 11, residue 324. -/
theorem bounds_11_324 : exactInterval 11 324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_324 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 324) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_324 : oddCount 324 11 = 5 ∧ acceleratedOrbit 11 324 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_324 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 324) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_324.1, data_11_324.2]

/-- Complete interval computation for depth 11, residue 325. -/
theorem bounds_11_325 : exactInterval 11 325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_325 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 325) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_325 : oddCount 325 11 = 5 ∧ acceleratedOrbit 11 325 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_325 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 325) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_325.1, data_11_325.2]

/-- Complete interval computation for depth 11, residue 326. -/
theorem bounds_11_326 : exactInterval 11 326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_326 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 326) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_326 : oddCount 326 11 = 5 ∧ acceleratedOrbit 11 326 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_326 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 326) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_326.1, data_11_326.2]

end Collatz.Research.StoppingAtlas.Batch0088
