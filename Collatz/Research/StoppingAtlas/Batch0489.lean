import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0489

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 327. -/
theorem bounds_13_327 : exactInterval 13 327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_327 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 327) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_327 : oddCount 327 13 = 10 ∧ acceleratedOrbit 13 327 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_327 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 327) = 3 ^ 10 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_327.1, data_13_327.2]

/-- Complete interval computation for depth 13, residue 328. -/
theorem bounds_13_328 : exactInterval 13 328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_328 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 328) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_328 : oddCount 328 13 = 7 ∧ acceleratedOrbit 13 328 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_328 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 328) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_328.1, data_13_328.2]

/-- Complete interval computation for depth 13, residue 329. -/
theorem bounds_13_329 : exactInterval 13 329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_329 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 329) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_329 : oddCount 329 13 = 7 ∧ acceleratedOrbit 13 329 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_329 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 329) = 3 ^ 7 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_329.1, data_13_329.2]

/-- Complete interval computation for depth 13, residue 330. -/
theorem bounds_13_330 : exactInterval 13 330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_330 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 330) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_330 : oddCount 330 13 = 7 ∧ acceleratedOrbit 13 330 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_330 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 330) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_330.1, data_13_330.2]

/-- Complete interval computation for depth 13, residue 331. -/
theorem bounds_13_331 : exactInterval 13 331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_331 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 331) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_331 : oddCount 331 13 = 5 ∧ acceleratedOrbit 13 331 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_331 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 331) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_331.1, data_13_331.2]

/-- Complete interval computation for depth 13, residue 332. -/
theorem bounds_13_332 : exactInterval 13 332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_332 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 332) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_332 : oddCount 332 13 = 7 ∧ acceleratedOrbit 13 332 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_332 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 332) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_332.1, data_13_332.2]

/-- Complete interval computation for depth 13, residue 333. -/
theorem bounds_13_333 : exactInterval 13 333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_333 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 333) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_333 : oddCount 333 13 = 7 ∧ acceleratedOrbit 13 333 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_333 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 333) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_333.1, data_13_333.2]

/-- Complete interval computation for depth 13, residue 334. -/
theorem bounds_13_334 : exactInterval 13 334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_334 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 334) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_334 : oddCount 334 13 = 10 ∧ acceleratedOrbit 13 334 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_334 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 334) = 3 ^ 10 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_334.1, data_13_334.2]

/-- Complete interval computation for depth 13, residue 335. -/
theorem bounds_13_335 : exactInterval 13 335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_335 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 335) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_335 : oddCount 335 13 = 10 ∧ acceleratedOrbit 13 335 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_335 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 335) = 3 ^ 10 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_335.1, data_13_335.2]

/-- Complete interval computation for depth 13, residue 336. -/
theorem bounds_13_336 : exactInterval 13 336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_336 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 336) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_336 : oddCount 336 13 = 3 ∧ acceleratedOrbit 13 336 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_336 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 336) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_336.1, data_13_336.2]

/-- Complete interval computation for depth 13, residue 337. -/
theorem bounds_13_337 : exactInterval 13 337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_337 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 337) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_337 : oddCount 337 13 = 7 ∧ acceleratedOrbit 13 337 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_337 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 337) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_337.1, data_13_337.2]

/-- Complete interval computation for depth 13, residue 338. -/
theorem bounds_13_338 : exactInterval 13 338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_338 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 338) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_338 : oddCount 338 13 = 9 ∧ acceleratedOrbit 13 338 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_338 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 338) = 3 ^ 9 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_338.1, data_13_338.2]

/-- Complete interval computation for depth 13, residue 339. -/
theorem bounds_13_339 : exactInterval 13 339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_339 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 339) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_339 : oddCount 339 13 = 9 ∧ acceleratedOrbit 13 339 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_339 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 339) = 3 ^ 9 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_339.1, data_13_339.2]

/-- Complete interval computation for depth 13, residue 340. -/
theorem bounds_13_340 : exactInterval 13 340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_340 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 340) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_340 : oddCount 340 13 = 3 ∧ acceleratedOrbit 13 340 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_340 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 340) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_340.1, data_13_340.2]

/-- Complete interval computation for depth 13, residue 341. -/
theorem bounds_13_341 : exactInterval 13 341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_341 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 341) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_341 : oddCount 341 13 = 3 ∧ acceleratedOrbit 13 341 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_341 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 341) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_341.1, data_13_341.2]

/-- Complete interval computation for depth 13, residue 342. -/
theorem bounds_13_342 : exactInterval 13 342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_342 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 342) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_342 : oddCount 342 13 = 6 ∧ acceleratedOrbit 13 342 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_342 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 342) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_342.1, data_13_342.2]

end Collatz.Research.StoppingAtlas.Batch0489
