import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0223

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 337. -/
theorem bounds_12_337 : exactInterval 12 337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_337 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 337) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_337 : oddCount 337 12 = 7 ∧ acceleratedOrbit 12 337 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_337 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 337) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_337.1, data_12_337.2]

/-- Complete interval computation for depth 12, residue 338. -/
theorem bounds_12_338 : exactInterval 12 338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_338 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 338) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_338 : oddCount 338 12 = 9 ∧ acceleratedOrbit 12 338 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_338 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 338) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_338.1, data_12_338.2]

/-- Complete interval computation for depth 12, residue 339. -/
theorem bounds_12_339 : exactInterval 12 339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_339 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 339) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_339 : oddCount 339 12 = 9 ∧ acceleratedOrbit 12 339 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_339 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 339) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_339.1, data_12_339.2]

/-- Complete interval computation for depth 12, residue 340. -/
theorem bounds_12_340 : exactInterval 12 340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_340 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 340) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_340 : oddCount 340 12 = 2 ∧ acceleratedOrbit 12 340 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_340 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 340) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_340.1, data_12_340.2]

/-- Complete interval computation for depth 12, residue 341. -/
theorem bounds_12_341 : exactInterval 12 341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_341 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 341) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_341 : oddCount 341 12 = 2 ∧ acceleratedOrbit 12 341 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_341 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 341) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_341.1, data_12_341.2]

/-- Complete interval computation for depth 12, residue 342. -/
theorem bounds_12_342 : exactInterval 12 342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_342 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 342) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_342 : oddCount 342 12 = 6 ∧ acceleratedOrbit 12 342 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_342 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 342) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_342.1, data_12_342.2]

/-- Complete interval computation for depth 12, residue 343. -/
theorem bounds_12_343 : exactInterval 12 343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_343 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 343) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_343 : oddCount 343 12 = 6 ∧ acceleratedOrbit 12 343 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_343 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 343) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_343.1, data_12_343.2]

/-- Complete interval computation for depth 12, residue 344. -/
theorem bounds_12_344 : exactInterval 12 344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_344 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 344) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_344 : oddCount 344 12 = 4 ∧ acceleratedOrbit 12 344 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_344 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 344) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_344.1, data_12_344.2]

/-- Complete interval computation for depth 12, residue 345. -/
theorem bounds_12_345 : exactInterval 12 345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_345 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 345) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_345 : oddCount 345 12 = 7 ∧ acceleratedOrbit 12 345 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_345 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 345) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_345.1, data_12_345.2]

/-- Complete interval computation for depth 12, residue 346. -/
theorem bounds_12_346 : exactInterval 12 346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_346 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 346) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_346 : oddCount 346 12 = 4 ∧ acceleratedOrbit 12 346 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_346 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 346) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_346.1, data_12_346.2]

/-- Complete interval computation for depth 12, residue 347. -/
theorem bounds_12_347 : exactInterval 12 347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_347 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 347) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_347 : oddCount 347 12 = 6 ∧ acceleratedOrbit 12 347 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_347 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 347) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_347.1, data_12_347.2]

/-- Complete interval computation for depth 12, residue 348. -/
theorem bounds_12_348 : exactInterval 12 348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_348 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 348) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_348 : oddCount 348 12 = 4 ∧ acceleratedOrbit 12 348 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_348 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 348) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_348.1, data_12_348.2]

/-- Complete interval computation for depth 12, residue 349. -/
theorem bounds_12_349 : exactInterval 12 349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_349 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 349) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_349 : oddCount 349 12 = 4 ∧ acceleratedOrbit 12 349 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_349 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 349) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_349.1, data_12_349.2]

/-- Complete interval computation for depth 12, residue 350. -/
theorem bounds_12_350 : exactInterval 12 350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_350 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 350) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_350 : oddCount 350 12 = 8 ∧ acceleratedOrbit 12 350 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_350 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 350) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_350.1, data_12_350.2]

/-- Complete interval computation for depth 12, residue 351. -/
theorem bounds_12_351 : exactInterval 12 351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_351 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 351) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_351 : oddCount 351 12 = 8 ∧ acceleratedOrbit 12 351 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_351 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 351) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_351.1, data_12_351.2]

/-- Complete interval computation for depth 12, residue 352. -/
theorem bounds_12_352 : exactInterval 12 352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_352 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 352) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_352 : oddCount 352 12 = 4 ∧ acceleratedOrbit 12 352 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_352 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 352) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_352.1, data_12_352.2]

end Collatz.Research.StoppingAtlas.Batch0223
