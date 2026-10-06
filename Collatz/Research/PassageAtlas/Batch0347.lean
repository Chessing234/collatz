import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0347

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11337. -/
theorem bounds_15_11337 : exactInterval 15 11337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11337 : oddCount 11337 15 = 9 ∧ acceleratedOrbit 15 11337 = 6812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11337) = 3 ^ 9 * m + 6812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11337.1, data_15_11337.2]

/-- Complete interval computation for depth 15, residue 11338. -/
theorem bounds_15_11338 : exactInterval 15 11338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11338 : oddCount 11338 15 = 7 ∧ acceleratedOrbit 15 11338 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11338) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11338.1, data_15_11338.2]

/-- Complete interval computation for depth 15, residue 11339. -/
theorem bounds_15_11339 : exactInterval 15 11339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11339 : oddCount 11339 15 = 6 ∧ acceleratedOrbit 15 11339 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11339) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11339.1, data_15_11339.2]

/-- Complete interval computation for depth 15, residue 11340. -/
theorem bounds_15_11340 : exactInterval 15 11340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11340 : oddCount 11340 15 = 7 ∧ acceleratedOrbit 15 11340 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11340) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11340.1, data_15_11340.2]

/-- Complete interval computation for depth 15, residue 11341. -/
theorem bounds_15_11341 : exactInterval 15 11341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11341 : oddCount 11341 15 = 7 ∧ acceleratedOrbit 15 11341 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11341) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11341.1, data_15_11341.2]

/-- Complete interval computation for depth 15, residue 11342. -/
theorem bounds_15_11342 : exactInterval 15 11342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11342 : oddCount 11342 15 = 7 ∧ acceleratedOrbit 15 11342 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11342) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11342.1, data_15_11342.2]

/-- Complete interval computation for depth 15, residue 11343. -/
theorem bounds_15_11343 : exactInterval 15 11343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11343 : oddCount 11343 15 = 7 ∧ acceleratedOrbit 15 11343 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11343) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11343.1, data_15_11343.2]

/-- Complete interval computation for depth 15, residue 11344. -/
theorem bounds_15_11344 : exactInterval 15 11344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11344 : oddCount 11344 15 = 4 ∧ acceleratedOrbit 15 11344 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11344) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11344.1, data_15_11344.2]

/-- Complete interval computation for depth 15, residue 11345. -/
theorem bounds_15_11345 : exactInterval 15 11345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11345 : oddCount 11345 15 = 7 ∧ acceleratedOrbit 15 11345 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11345) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11345.1, data_15_11345.2]

/-- Complete interval computation for depth 15, residue 11346. -/
theorem bounds_15_11346 : exactInterval 15 11346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11346 : oddCount 11346 15 = 11 ∧ acceleratedOrbit 15 11346 = 61357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11346) = 3 ^ 11 * m + 61357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11346.1, data_15_11346.2]

/-- Complete interval computation for depth 15, residue 11347. -/
theorem bounds_15_11347 : exactInterval 15 11347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11347 : oddCount 11347 15 = 11 ∧ acceleratedOrbit 15 11347 = 61357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11347) = 3 ^ 11 * m + 61357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11347.1, data_15_11347.2]

/-- Complete interval computation for depth 15, residue 11348. -/
theorem bounds_15_11348 : exactInterval 15 11348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11348 : oddCount 11348 15 = 4 ∧ acceleratedOrbit 15 11348 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11348) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11348.1, data_15_11348.2]

/-- Complete interval computation for depth 15, residue 11349. -/
theorem bounds_15_11349 : exactInterval 15 11349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11349 : oddCount 11349 15 = 4 ∧ acceleratedOrbit 15 11349 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11349) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11349.1, data_15_11349.2]

/-- Complete interval computation for depth 15, residue 11350. -/
theorem bounds_15_11350 : exactInterval 15 11350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11350 : oddCount 11350 15 = 6 ∧ acceleratedOrbit 15 11350 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11350) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11350.1, data_15_11350.2]

/-- Complete interval computation for depth 15, residue 11351. -/
theorem bounds_15_11351 : exactInterval 15 11351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11351 : oddCount 11351 15 = 6 ∧ acceleratedOrbit 15 11351 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11351) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11351.1, data_15_11351.2]

/-- Complete interval computation for depth 15, residue 11352. -/
theorem bounds_15_11352 : exactInterval 15 11352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11352 : oddCount 11352 15 = 6 ∧ acceleratedOrbit 15 11352 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11352) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11352.1, data_15_11352.2]

/-- Complete interval computation for depth 15, residue 11353. -/
theorem bounds_15_11353 : exactInterval 15 11353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11353 : oddCount 11353 15 = 9 ∧ acceleratedOrbit 15 11353 = 6824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11353) = 3 ^ 9 * m + 6824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11353.1, data_15_11353.2]

/-- Complete interval computation for depth 15, residue 11354. -/
theorem bounds_15_11354 : exactInterval 15 11354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11354 : oddCount 11354 15 = 6 ∧ acceleratedOrbit 15 11354 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11354) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11354.1, data_15_11354.2]

/-- Complete interval computation for depth 15, residue 11355. -/
theorem bounds_15_11355 : exactInterval 15 11355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11355 : oddCount 11355 15 = 11 ∧ acceleratedOrbit 15 11355 = 61397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11355) = 3 ^ 11 * m + 61397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11355.1, data_15_11355.2]

/-- Complete interval computation for depth 15, residue 11356. -/
theorem bounds_15_11356 : exactInterval 15 11356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11356 : oddCount 11356 15 = 6 ∧ acceleratedOrbit 15 11356 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11356) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11356.1, data_15_11356.2]

/-- Complete interval computation for depth 15, residue 11357. -/
theorem bounds_15_11357 : exactInterval 15 11357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11357 : oddCount 11357 15 = 6 ∧ acceleratedOrbit 15 11357 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11357) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11357.1, data_15_11357.2]

/-- Complete interval computation for depth 15, residue 11358. -/
theorem bounds_15_11358 : exactInterval 15 11358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11358 : oddCount 11358 15 = 11 ∧ acceleratedOrbit 15 11358 = 61418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11358) = 3 ^ 11 * m + 61418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11358.1, data_15_11358.2]

/-- Complete interval computation for depth 15, residue 11359. -/
theorem bounds_15_11359 : exactInterval 15 11359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11359 : oddCount 11359 15 = 11 ∧ acceleratedOrbit 15 11359 = 61418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11359) = 3 ^ 11 * m + 61418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11359.1, data_15_11359.2]

/-- Complete interval computation for depth 15, residue 11360. -/
theorem bounds_15_11360 : exactInterval 15 11360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11360 : oddCount 11360 15 = 4 ∧ acceleratedOrbit 15 11360 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11360) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11360.1, data_15_11360.2]

/-- Complete interval computation for depth 15, residue 11361. -/
theorem bounds_15_11361 : exactInterval 15 11361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11361 : oddCount 11361 15 = 8 ∧ acceleratedOrbit 15 11361 = 2276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11361) = 3 ^ 8 * m + 2276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11361.1, data_15_11361.2]

/-- Complete interval computation for depth 15, residue 11362. -/
theorem bounds_15_11362 : exactInterval 15 11362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11362 : oddCount 11362 15 = 8 ∧ acceleratedOrbit 15 11362 = 2278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11362) = 3 ^ 8 * m + 2278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11362.1, data_15_11362.2]

/-- Complete interval computation for depth 15, residue 11363. -/
theorem bounds_15_11363 : exactInterval 15 11363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11363 : oddCount 11363 15 = 8 ∧ acceleratedOrbit 15 11363 = 2278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11363) = 3 ^ 8 * m + 2278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11363.1, data_15_11363.2]

/-- Complete interval computation for depth 15, residue 11364. -/
theorem bounds_15_11364 : exactInterval 15 11364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11364 : oddCount 11364 15 = 8 ∧ acceleratedOrbit 15 11364 = 2278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11364) = 3 ^ 8 * m + 2278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11364.1, data_15_11364.2]

/-- Complete interval computation for depth 15, residue 11365. -/
theorem bounds_15_11365 : exactInterval 15 11365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11365 : oddCount 11365 15 = 8 ∧ acceleratedOrbit 15 11365 = 2278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11365) = 3 ^ 8 * m + 2278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11365.1, data_15_11365.2]

/-- Complete interval computation for depth 15, residue 11366. -/
theorem bounds_15_11366 : exactInterval 15 11366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11366 : oddCount 11366 15 = 8 ∧ acceleratedOrbit 15 11366 = 2278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11366) = 3 ^ 8 * m + 2278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11366.1, data_15_11366.2]

/-- Complete interval computation for depth 15, residue 11367. -/
theorem bounds_15_11367 : exactInterval 15 11367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11367 : oddCount 11367 15 = 12 ∧ acceleratedOrbit 15 11367 = 184376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11367) = 3 ^ 12 * m + 184376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11367.1, data_15_11367.2]

/-- Complete interval computation for depth 15, residue 11368. -/
theorem bounds_15_11368 : exactInterval 15 11368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11368 : oddCount 11368 15 = 4 ∧ acceleratedOrbit 15 11368 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11368) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11368.1, data_15_11368.2]

/-- Complete interval computation for depth 15, residue 11369. -/
theorem bounds_15_11369 : exactInterval 15 11369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11369 : oddCount 11369 15 = 11 ∧ acceleratedOrbit 15 11369 = 61478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11369) = 3 ^ 11 * m + 61478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11369.1, data_15_11369.2]

end Collatz.Research.PassageAtlas.Batch0347
