import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0011

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 327. -/
theorem bounds_15_327 : exactInterval 15 327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_327 : oddCount 327 15 = 11 ∧ acceleratedOrbit 15 327 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 327) = 3 ^ 11 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_327.1, data_15_327.2]

/-- Complete interval computation for depth 15, residue 328. -/
theorem bounds_15_328 : exactInterval 15 328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_328 : oddCount 328 15 = 9 ∧ acceleratedOrbit 15 328 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 328) = 3 ^ 9 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_328.1, data_15_328.2]

/-- Complete interval computation for depth 15, residue 329. -/
theorem bounds_15_329 : exactInterval 15 329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_329 : oddCount 329 15 = 8 ∧ acceleratedOrbit 15 329 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 329) = 3 ^ 8 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_329.1, data_15_329.2]

/-- Complete interval computation for depth 15, residue 330. -/
theorem bounds_15_330 : exactInterval 15 330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_330 : oddCount 330 15 = 9 ∧ acceleratedOrbit 15 330 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 330) = 3 ^ 9 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_330.1, data_15_330.2]

/-- Complete interval computation for depth 15, residue 331. -/
theorem bounds_15_331 : exactInterval 15 331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_331 : oddCount 331 15 = 6 ∧ acceleratedOrbit 15 331 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 331) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_331.1, data_15_331.2]

/-- Complete interval computation for depth 15, residue 332. -/
theorem bounds_15_332 : exactInterval 15 332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_332 : oddCount 332 15 = 9 ∧ acceleratedOrbit 15 332 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 332) = 3 ^ 9 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_332.1, data_15_332.2]

/-- Complete interval computation for depth 15, residue 333. -/
theorem bounds_15_333 : exactInterval 15 333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_333 : oddCount 333 15 = 9 ∧ acceleratedOrbit 15 333 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 333) = 3 ^ 9 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_333.1, data_15_333.2]

/-- Complete interval computation for depth 15, residue 334. -/
theorem bounds_15_334 : exactInterval 15 334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_334 : oddCount 334 15 = 11 ∧ acceleratedOrbit 15 334 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 334) = 3 ^ 11 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_334.1, data_15_334.2]

/-- Complete interval computation for depth 15, residue 335. -/
theorem bounds_15_335 : exactInterval 15 335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_335 : oddCount 335 15 = 11 ∧ acceleratedOrbit 15 335 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 335) = 3 ^ 11 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_335.1, data_15_335.2]

/-- Complete interval computation for depth 15, residue 336. -/
theorem bounds_15_336 : exactInterval 15 336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_336 : oddCount 336 15 = 4 ∧ acceleratedOrbit 15 336 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 336) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_336.1, data_15_336.2]

/-- Complete interval computation for depth 15, residue 337. -/
theorem bounds_15_337 : exactInterval 15 337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_337 : oddCount 337 15 = 9 ∧ acceleratedOrbit 15 337 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 337) = 3 ^ 9 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_337.1, data_15_337.2]

/-- Complete interval computation for depth 15, residue 338. -/
theorem bounds_15_338 : exactInterval 15 338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_338 : oddCount 338 15 = 9 ∧ acceleratedOrbit 15 338 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 338) = 3 ^ 9 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_338.1, data_15_338.2]

/-- Complete interval computation for depth 15, residue 339. -/
theorem bounds_15_339 : exactInterval 15 339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_339 : oddCount 339 15 = 9 ∧ acceleratedOrbit 15 339 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 339) = 3 ^ 9 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_339.1, data_15_339.2]

/-- Complete interval computation for depth 15, residue 340. -/
theorem bounds_15_340 : exactInterval 15 340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_340 : oddCount 340 15 = 4 ∧ acceleratedOrbit 15 340 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 340) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_340.1, data_15_340.2]

/-- Complete interval computation for depth 15, residue 341. -/
theorem bounds_15_341 : exactInterval 15 341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_341 : oddCount 341 15 = 4 ∧ acceleratedOrbit 15 341 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 341) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_341.1, data_15_341.2]

/-- Complete interval computation for depth 15, residue 342. -/
theorem bounds_15_342 : exactInterval 15 342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_342 : oddCount 342 15 = 8 ∧ acceleratedOrbit 15 342 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 342) = 3 ^ 8 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_342.1, data_15_342.2]

/-- Complete interval computation for depth 15, residue 343. -/
theorem bounds_15_343 : exactInterval 15 343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_343 : oddCount 343 15 = 8 ∧ acceleratedOrbit 15 343 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 343) = 3 ^ 8 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_343.1, data_15_343.2]

/-- Complete interval computation for depth 15, residue 344. -/
theorem bounds_15_344 : exactInterval 15 344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_344 : oddCount 344 15 = 7 ∧ acceleratedOrbit 15 344 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 344) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_344.1, data_15_344.2]

/-- Complete interval computation for depth 15, residue 345. -/
theorem bounds_15_345 : exactInterval 15 345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_345 : oddCount 345 15 = 8 ∧ acceleratedOrbit 15 345 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 345) = 3 ^ 8 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_345.1, data_15_345.2]

/-- Complete interval computation for depth 15, residue 346. -/
theorem bounds_15_346 : exactInterval 15 346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_346 : oddCount 346 15 = 7 ∧ acceleratedOrbit 15 346 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 346) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_346.1, data_15_346.2]

/-- Complete interval computation for depth 15, residue 347. -/
theorem bounds_15_347 : exactInterval 15 347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_347 : oddCount 347 15 = 8 ∧ acceleratedOrbit 15 347 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 347) = 3 ^ 8 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_347.1, data_15_347.2]

/-- Complete interval computation for depth 15, residue 348. -/
theorem bounds_15_348 : exactInterval 15 348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_348 : oddCount 348 15 = 7 ∧ acceleratedOrbit 15 348 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 348) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_348.1, data_15_348.2]

/-- Complete interval computation for depth 15, residue 349. -/
theorem bounds_15_349 : exactInterval 15 349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_349 : oddCount 349 15 = 7 ∧ acceleratedOrbit 15 349 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 349) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_349.1, data_15_349.2]

/-- Complete interval computation for depth 15, residue 350. -/
theorem bounds_15_350 : exactInterval 15 350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_350 : oddCount 350 15 = 10 ∧ acceleratedOrbit 15 350 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 350) = 3 ^ 10 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_350.1, data_15_350.2]

/-- Complete interval computation for depth 15, residue 351. -/
theorem bounds_15_351 : exactInterval 15 351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_351 : oddCount 351 15 = 10 ∧ acceleratedOrbit 15 351 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 351) = 3 ^ 10 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_351.1, data_15_351.2]

/-- Complete interval computation for depth 15, residue 352. -/
theorem bounds_15_352 : exactInterval 15 352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_352 : oddCount 352 15 = 4 ∧ acceleratedOrbit 15 352 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 352) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_352.1, data_15_352.2]

/-- Complete interval computation for depth 15, residue 353. -/
theorem bounds_15_353 : exactInterval 15 353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_353 : oddCount 353 15 = 9 ∧ acceleratedOrbit 15 353 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 353) = 3 ^ 9 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_353.1, data_15_353.2]

/-- Complete interval computation for depth 15, residue 354. -/
theorem bounds_15_354 : exactInterval 15 354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_354 : oddCount 354 15 = 7 ∧ acceleratedOrbit 15 354 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 354) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_354.1, data_15_354.2]

/-- Complete interval computation for depth 15, residue 355. -/
theorem bounds_15_355 : exactInterval 15 355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_355 : oddCount 355 15 = 7 ∧ acceleratedOrbit 15 355 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 355) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_355.1, data_15_355.2]

/-- Complete interval computation for depth 15, residue 356. -/
theorem bounds_15_356 : exactInterval 15 356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_356 : oddCount 356 15 = 7 ∧ acceleratedOrbit 15 356 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 356) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_356.1, data_15_356.2]

/-- Complete interval computation for depth 15, residue 357. -/
theorem bounds_15_357 : exactInterval 15 357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_357 : oddCount 357 15 = 7 ∧ acceleratedOrbit 15 357 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 357) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_357.1, data_15_357.2]

/-- Complete interval computation for depth 15, residue 358. -/
theorem bounds_15_358 : exactInterval 15 358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_358 : oddCount 358 15 = 7 ∧ acceleratedOrbit 15 358 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 358) = 3 ^ 7 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_358.1, data_15_358.2]

/-- Complete interval computation for depth 15, residue 359. -/
theorem bounds_15_359 : exactInterval 15 359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_359 : oddCount 359 15 = 10 ∧ acceleratedOrbit 15 359 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 359) = 3 ^ 10 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_359.1, data_15_359.2]

end Collatz.Research.PassageAtlas.Batch0011
