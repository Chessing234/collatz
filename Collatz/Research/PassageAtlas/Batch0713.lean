import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0713

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23330. -/
theorem bounds_15_23330 : exactInterval 15 23330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23330 : oddCount 23330 15 = 7 ∧ acceleratedOrbit 15 23330 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23330) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23330.1, data_15_23330.2]

/-- Complete interval computation for depth 15, residue 23331. -/
theorem bounds_15_23331 : exactInterval 15 23331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23331 : oddCount 23331 15 = 7 ∧ acceleratedOrbit 15 23331 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23331) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23331.1, data_15_23331.2]

/-- Complete interval computation for depth 15, residue 23332. -/
theorem bounds_15_23332 : exactInterval 15 23332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23332 : oddCount 23332 15 = 7 ∧ acceleratedOrbit 15 23332 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23332) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23332.1, data_15_23332.2]

/-- Complete interval computation for depth 15, residue 23333. -/
theorem bounds_15_23333 : exactInterval 15 23333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23333 : oddCount 23333 15 = 7 ∧ acceleratedOrbit 15 23333 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23333) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23333.1, data_15_23333.2]

/-- Complete interval computation for depth 15, residue 23334. -/
theorem bounds_15_23334 : exactInterval 15 23334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23334 : oddCount 23334 15 = 7 ∧ acceleratedOrbit 15 23334 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23334) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23334.1, data_15_23334.2]

/-- Complete interval computation for depth 15, residue 23335. -/
theorem bounds_15_23335 : exactInterval 15 23335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23335 : oddCount 23335 15 = 9 ∧ acceleratedOrbit 15 23335 = 14018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23335) = 3 ^ 9 * m + 14018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23335.1, data_15_23335.2]

/-- Complete interval computation for depth 15, residue 23336. -/
theorem bounds_15_23336 : exactInterval 15 23336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23336 : oddCount 23336 15 = 4 ∧ acceleratedOrbit 15 23336 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23336) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23336.1, data_15_23336.2]

/-- Complete interval computation for depth 15, residue 23337. -/
theorem bounds_15_23337 : exactInterval 15 23337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23337 : oddCount 23337 15 = 10 ∧ acceleratedOrbit 15 23337 = 42059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23337) = 3 ^ 10 * m + 42059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23337.1, data_15_23337.2]

/-- Complete interval computation for depth 15, residue 23338. -/
theorem bounds_15_23338 : exactInterval 15 23338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23338 : oddCount 23338 15 = 4 ∧ acceleratedOrbit 15 23338 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23338) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23338.1, data_15_23338.2]

/-- Complete interval computation for depth 15, residue 23339. -/
theorem bounds_15_23339 : exactInterval 15 23339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23339 : oddCount 23339 15 = 7 ∧ acceleratedOrbit 15 23339 = 1558 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23339) = 3 ^ 7 * m + 1558 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23339.1, data_15_23339.2]

/-- Complete interval computation for depth 15, residue 23340. -/
theorem bounds_15_23340 : exactInterval 15 23340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23340 : oddCount 23340 15 = 7 ∧ acceleratedOrbit 15 23340 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23340) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23340.1, data_15_23340.2]

/-- Complete interval computation for depth 15, residue 23341. -/
theorem bounds_15_23341 : exactInterval 15 23341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23341 : oddCount 23341 15 = 7 ∧ acceleratedOrbit 15 23341 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23341) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23341.1, data_15_23341.2]

/-- Complete interval computation for depth 15, residue 23342. -/
theorem bounds_15_23342 : exactInterval 15 23342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23342 : oddCount 23342 15 = 7 ∧ acceleratedOrbit 15 23342 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23342) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23342.1, data_15_23342.2]

/-- Complete interval computation for depth 15, residue 23343. -/
theorem bounds_15_23343 : exactInterval 15 23343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23343 : oddCount 23343 15 = 9 ∧ acceleratedOrbit 15 23343 = 14023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23343) = 3 ^ 9 * m + 14023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23343.1, data_15_23343.2]

/-- Complete interval computation for depth 15, residue 23344. -/
theorem bounds_15_23344 : exactInterval 15 23344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23344 : oddCount 23344 15 = 4 ∧ acceleratedOrbit 15 23344 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23344) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23344.1, data_15_23344.2]

/-- Complete interval computation for depth 15, residue 23345. -/
theorem bounds_15_23345 : exactInterval 15 23345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23345 : oddCount 23345 15 = 7 ∧ acceleratedOrbit 15 23345 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23345) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23345.1, data_15_23345.2]

/-- Complete interval computation for depth 15, residue 23346. -/
theorem bounds_15_23346 : exactInterval 15 23346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23346 : oddCount 23346 15 = 7 ∧ acceleratedOrbit 15 23346 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23346) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23346.1, data_15_23346.2]

/-- Complete interval computation for depth 15, residue 23347. -/
theorem bounds_15_23347 : exactInterval 15 23347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23347 : oddCount 23347 15 = 7 ∧ acceleratedOrbit 15 23347 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23347) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23347.1, data_15_23347.2]

/-- Complete interval computation for depth 15, residue 23348. -/
theorem bounds_15_23348 : exactInterval 15 23348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23348 : oddCount 23348 15 = 4 ∧ acceleratedOrbit 15 23348 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23348) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23348.1, data_15_23348.2]

/-- Complete interval computation for depth 15, residue 23349. -/
theorem bounds_15_23349 : exactInterval 15 23349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23349 : oddCount 23349 15 = 4 ∧ acceleratedOrbit 15 23349 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23349) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23349.1, data_15_23349.2]

/-- Complete interval computation for depth 15, residue 23350. -/
theorem bounds_15_23350 : exactInterval 15 23350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23350 : oddCount 23350 15 = 8 ∧ acceleratedOrbit 15 23350 = 4676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23350) = 3 ^ 8 * m + 4676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23350.1, data_15_23350.2]

/-- Complete interval computation for depth 15, residue 23351. -/
theorem bounds_15_23351 : exactInterval 15 23351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23351 : oddCount 23351 15 = 8 ∧ acceleratedOrbit 15 23351 = 4676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23351) = 3 ^ 8 * m + 4676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23351.1, data_15_23351.2]

/-- Complete interval computation for depth 15, residue 23352. -/
theorem bounds_15_23352 : exactInterval 15 23352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23352 : oddCount 23352 15 = 9 ∧ acceleratedOrbit 15 23352 = 14033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23352) = 3 ^ 9 * m + 14033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23352.1, data_15_23352.2]

/-- Complete interval computation for depth 15, residue 23353. -/
theorem bounds_15_23353 : exactInterval 15 23353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23353 : oddCount 23353 15 = 9 ∧ acceleratedOrbit 15 23353 = 14030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23353) = 3 ^ 9 * m + 14030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23353.1, data_15_23353.2]

/-- Complete interval computation for depth 15, residue 23354. -/
theorem bounds_15_23354 : exactInterval 15 23354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23354 : oddCount 23354 15 = 9 ∧ acceleratedOrbit 15 23354 = 14033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23354) = 3 ^ 9 * m + 14033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23354.1, data_15_23354.2]

/-- Complete interval computation for depth 15, residue 23355. -/
theorem bounds_15_23355 : exactInterval 15 23355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23355 : oddCount 23355 15 = 9 ∧ acceleratedOrbit 15 23355 = 14033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23355) = 3 ^ 9 * m + 14033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23355.1, data_15_23355.2]

/-- Complete interval computation for depth 15, residue 23356. -/
theorem bounds_15_23356 : exactInterval 15 23356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23356 : oddCount 23356 15 = 9 ∧ acceleratedOrbit 15 23356 = 14033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23356) = 3 ^ 9 * m + 14033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23356.1, data_15_23356.2]

/-- Complete interval computation for depth 15, residue 23357. -/
theorem bounds_15_23357 : exactInterval 15 23357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23357 : oddCount 23357 15 = 9 ∧ acceleratedOrbit 15 23357 = 14033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23357) = 3 ^ 9 * m + 14033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23357.1, data_15_23357.2]

/-- Complete interval computation for depth 15, residue 23358. -/
theorem bounds_15_23358 : exactInterval 15 23358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23358 : oddCount 23358 15 = 9 ∧ acceleratedOrbit 15 23358 = 14032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23358) = 3 ^ 9 * m + 14032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23358.1, data_15_23358.2]

/-- Complete interval computation for depth 15, residue 23359. -/
theorem bounds_15_23359 : exactInterval 15 23359 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23359) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23359 : oddCount 23359 15 = 9 ∧ acceleratedOrbit 15 23359 = 14032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23359) = 3 ^ 9 * m + 14032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23359.1, data_15_23359.2]

/-- Complete interval computation for depth 15, residue 23360. -/
theorem bounds_15_23360 : exactInterval 15 23360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23360 : oddCount 23360 15 = 5 ∧ acceleratedOrbit 15 23360 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23360) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23360.1, data_15_23360.2]

/-- Complete interval computation for depth 15, residue 23361. -/
theorem bounds_15_23361 : exactInterval 15 23361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23361 : oddCount 23361 15 = 4 ∧ acceleratedOrbit 15 23361 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23361) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23361.1, data_15_23361.2]

/-- Complete interval computation for depth 15, residue 23362. -/
theorem bounds_15_23362 : exactInterval 15 23362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23362 : oddCount 23362 15 = 9 ∧ acceleratedOrbit 15 23362 = 14039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23362) = 3 ^ 9 * m + 14039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23362.1, data_15_23362.2]

end Collatz.Research.PassageAtlas.Batch0713
