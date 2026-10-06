import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0089

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 327. -/
theorem bounds_11_327 : exactInterval 11 327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_327 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 327) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_327 : oddCount 327 11 = 9 ∧ acceleratedOrbit 11 327 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_327 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 327) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_327.1, data_11_327.2]

/-- Complete interval computation for depth 11, residue 328. -/
theorem bounds_11_328 : exactInterval 11 328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_328 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 328) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_328 : oddCount 328 11 = 6 ∧ acceleratedOrbit 11 328 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_328 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 328) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_328.1, data_11_328.2]

/-- Complete interval computation for depth 11, residue 329. -/
theorem bounds_11_329 : exactInterval 11 329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_329 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 329) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_329 : oddCount 329 11 = 6 ∧ acceleratedOrbit 11 329 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_329 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 329) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_329.1, data_11_329.2]

/-- Complete interval computation for depth 11, residue 330. -/
theorem bounds_11_330 : exactInterval 11 330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_330 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 330) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_330 : oddCount 330 11 = 6 ∧ acceleratedOrbit 11 330 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_330 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 330) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_330.1, data_11_330.2]

/-- Complete interval computation for depth 11, residue 331. -/
theorem bounds_11_331 : exactInterval 11 331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_331 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 331) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_331 : oddCount 331 11 = 5 ∧ acceleratedOrbit 11 331 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_331 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 331) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_331.1, data_11_331.2]

/-- Complete interval computation for depth 11, residue 332. -/
theorem bounds_11_332 : exactInterval 11 332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_332 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 332) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_332 : oddCount 332 11 = 6 ∧ acceleratedOrbit 11 332 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_332 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 332) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_332.1, data_11_332.2]

/-- Complete interval computation for depth 11, residue 333. -/
theorem bounds_11_333 : exactInterval 11 333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_333 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 333) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_333 : oddCount 333 11 = 6 ∧ acceleratedOrbit 11 333 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_333 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 333) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_333.1, data_11_333.2]

/-- Complete interval computation for depth 11, residue 334. -/
theorem bounds_11_334 : exactInterval 11 334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_334 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 334) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_334 : oddCount 334 11 = 8 ∧ acceleratedOrbit 11 334 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_334 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 334) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_334.1, data_11_334.2]

/-- Complete interval computation for depth 11, residue 335. -/
theorem bounds_11_335 : exactInterval 11 335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_335 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 335) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_335 : oddCount 335 11 = 8 ∧ acceleratedOrbit 11 335 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_335 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 335) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_335.1, data_11_335.2]

/-- Complete interval computation for depth 11, residue 336. -/
theorem bounds_11_336 : exactInterval 11 336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_336 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 336) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_336 : oddCount 336 11 = 2 ∧ acceleratedOrbit 11 336 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_336 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 336) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_336.1, data_11_336.2]

/-- Complete interval computation for depth 11, residue 337. -/
theorem bounds_11_337 : exactInterval 11 337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_337 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 337) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_337 : oddCount 337 11 = 7 ∧ acceleratedOrbit 11 337 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_337 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 337) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_337.1, data_11_337.2]

/-- Complete interval computation for depth 11, residue 338. -/
theorem bounds_11_338 : exactInterval 11 338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_338 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 338) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_338 : oddCount 338 11 = 8 ∧ acceleratedOrbit 11 338 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_338 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 338) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_338.1, data_11_338.2]

/-- Complete interval computation for depth 11, residue 339. -/
theorem bounds_11_339 : exactInterval 11 339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_339 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 339) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_339 : oddCount 339 11 = 8 ∧ acceleratedOrbit 11 339 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_339 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 339) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_339.1, data_11_339.2]

/-- Complete interval computation for depth 11, residue 340. -/
theorem bounds_11_340 : exactInterval 11 340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_340 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 340) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_340 : oddCount 340 11 = 2 ∧ acceleratedOrbit 11 340 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_340 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 340) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_340.1, data_11_340.2]

/-- Complete interval computation for depth 11, residue 341. -/
theorem bounds_11_341 : exactInterval 11 341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_341 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 341) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_341 : oddCount 341 11 = 2 ∧ acceleratedOrbit 11 341 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_341 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 341) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_341.1, data_11_341.2]

/-- Complete interval computation for depth 11, residue 342. -/
theorem bounds_11_342 : exactInterval 11 342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_342 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 342) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_342 : oddCount 342 11 = 5 ∧ acceleratedOrbit 11 342 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_342 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 342) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_342.1, data_11_342.2]

end Collatz.Research.StoppingAtlas.Batch0089
