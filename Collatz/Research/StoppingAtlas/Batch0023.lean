import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0023

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 337. -/
theorem bounds_10_337 : exactInterval 10 337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_337 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 337) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_337 : oddCount 337 10 = 7 ∧ acceleratedOrbit 10 337 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_337 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 337) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_337.1, data_10_337.2]

/-- Complete interval computation for depth 10, residue 338. -/
theorem bounds_10_338 : exactInterval 10 338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_338 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 338) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_338 : oddCount 338 10 = 8 ∧ acceleratedOrbit 10 338 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_338 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 338) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_338.1, data_10_338.2]

/-- Complete interval computation for depth 10, residue 339. -/
theorem bounds_10_339 : exactInterval 10 339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_339 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 339) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_339 : oddCount 339 10 = 8 ∧ acceleratedOrbit 10 339 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_339 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 339) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_339.1, data_10_339.2]

/-- Complete interval computation for depth 10, residue 340. -/
theorem bounds_10_340 : exactInterval 10 340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_340 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 340) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_340 : oddCount 340 10 = 1 ∧ acceleratedOrbit 10 340 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_340 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 340) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_340.1, data_10_340.2]

/-- Complete interval computation for depth 10, residue 341. -/
theorem bounds_10_341 : exactInterval 10 341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_341 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 341) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_341 : oddCount 341 10 = 1 ∧ acceleratedOrbit 10 341 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_341 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 341) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_341.1, data_10_341.2]

/-- Complete interval computation for depth 10, residue 342. -/
theorem bounds_10_342 : exactInterval 10 342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_342 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 342) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_342 : oddCount 342 10 = 5 ∧ acceleratedOrbit 10 342 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_342 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 342) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_342.1, data_10_342.2]

/-- Complete interval computation for depth 10, residue 343. -/
theorem bounds_10_343 : exactInterval 10 343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_343 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 343) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_343 : oddCount 343 10 = 5 ∧ acceleratedOrbit 10 343 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_343 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 343) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_343.1, data_10_343.2]

/-- Complete interval computation for depth 10, residue 344. -/
theorem bounds_10_344 : exactInterval 10 344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_344 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 344) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_344 : oddCount 344 10 = 4 ∧ acceleratedOrbit 10 344 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_344 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 344) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_344.1, data_10_344.2]

/-- Complete interval computation for depth 10, residue 345. -/
theorem bounds_10_345 : exactInterval 10 345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_345 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 345) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_345 : oddCount 345 10 = 5 ∧ acceleratedOrbit 10 345 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_345 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 345) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_345.1, data_10_345.2]

/-- Complete interval computation for depth 10, residue 346. -/
theorem bounds_10_346 : exactInterval 10 346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_346 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 346) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_346 : oddCount 346 10 = 4 ∧ acceleratedOrbit 10 346 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_346 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 346) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_346.1, data_10_346.2]

/-- Complete interval computation for depth 10, residue 347. -/
theorem bounds_10_347 : exactInterval 10 347 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_347 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 347) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_347 : oddCount 347 10 = 6 ∧ acceleratedOrbit 10 347 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_347 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 347) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_347.1, data_10_347.2]

/-- Complete interval computation for depth 10, residue 348. -/
theorem bounds_10_348 : exactInterval 10 348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_348 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 348) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_348 : oddCount 348 10 = 4 ∧ acceleratedOrbit 10 348 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_348 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 348) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_348.1, data_10_348.2]

/-- Complete interval computation for depth 10, residue 349. -/
theorem bounds_10_349 : exactInterval 10 349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_349 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 349) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_349 : oddCount 349 10 = 4 ∧ acceleratedOrbit 10 349 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_349 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 349) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_349.1, data_10_349.2]

/-- Complete interval computation for depth 10, residue 350. -/
theorem bounds_10_350 : exactInterval 10 350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_350 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 350) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_350 : oddCount 350 10 = 6 ∧ acceleratedOrbit 10 350 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_350 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 350) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_350.1, data_10_350.2]

/-- Complete interval computation for depth 10, residue 351. -/
theorem bounds_10_351 : exactInterval 10 351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_351 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 351) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_351 : oddCount 351 10 = 6 ∧ acceleratedOrbit 10 351 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_351 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 351) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_351.1, data_10_351.2]

/-- Complete interval computation for depth 10, residue 352. -/
theorem bounds_10_352 : exactInterval 10 352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_352 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 352) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_352 : oddCount 352 10 = 3 ∧ acceleratedOrbit 10 352 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_352 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 352) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_352.1, data_10_352.2]

end Collatz.Research.StoppingAtlas.Batch0023
