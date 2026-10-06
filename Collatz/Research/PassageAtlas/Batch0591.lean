import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0591

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19333. -/
theorem bounds_15_19333 : exactInterval 15 19333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19333 : oddCount 19333 15 = 10 ∧ acceleratedOrbit 15 19333 = 34856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19333) = 3 ^ 10 * m + 34856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19333.1, data_15_19333.2]

/-- Complete interval computation for depth 15, residue 19334. -/
theorem bounds_15_19334 : exactInterval 15 19334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19334 : oddCount 19334 15 = 10 ∧ acceleratedOrbit 15 19334 = 34856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19334) = 3 ^ 10 * m + 34856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19334.1, data_15_19334.2]

/-- Complete interval computation for depth 15, residue 19335. -/
theorem bounds_15_19335 : exactInterval 15 19335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19335 : oddCount 19335 15 = 7 ∧ acceleratedOrbit 15 19335 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19335) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19335.1, data_15_19335.2]

/-- Complete interval computation for depth 15, residue 19336. -/
theorem bounds_15_19336 : exactInterval 15 19336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19336 : oddCount 19336 15 = 3 ∧ acceleratedOrbit 15 19336 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19336) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19336.1, data_15_19336.2]

/-- Complete interval computation for depth 15, residue 19337. -/
theorem bounds_15_19337 : exactInterval 15 19337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19337 : oddCount 19337 15 = 10 ∧ acceleratedOrbit 15 19337 = 34850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19337) = 3 ^ 10 * m + 34850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19337.1, data_15_19337.2]

/-- Complete interval computation for depth 15, residue 19338. -/
theorem bounds_15_19338 : exactInterval 15 19338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19338 : oddCount 19338 15 = 3 ∧ acceleratedOrbit 15 19338 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19338) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19338.1, data_15_19338.2]

/-- Complete interval computation for depth 15, residue 19339. -/
theorem bounds_15_19339 : exactInterval 15 19339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19339 : oddCount 19339 15 = 10 ∧ acceleratedOrbit 15 19339 = 34856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19339) = 3 ^ 10 * m + 34856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19339.1, data_15_19339.2]

/-- Complete interval computation for depth 15, residue 19340. -/
theorem bounds_15_19340 : exactInterval 15 19340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19340 : oddCount 19340 15 = 3 ∧ acceleratedOrbit 15 19340 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19340) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19340.1, data_15_19340.2]

/-- Complete interval computation for depth 15, residue 19341. -/
theorem bounds_15_19341 : exactInterval 15 19341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19341 : oddCount 19341 15 = 3 ∧ acceleratedOrbit 15 19341 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19341) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19341.1, data_15_19341.2]

/-- Complete interval computation for depth 15, residue 19342. -/
theorem bounds_15_19342 : exactInterval 15 19342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19342 : oddCount 19342 15 = 8 ∧ acceleratedOrbit 15 19342 = 3874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19342) = 3 ^ 8 * m + 3874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19342.1, data_15_19342.2]

/-- Complete interval computation for depth 15, residue 19343. -/
theorem bounds_15_19343 : exactInterval 15 19343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19343 : oddCount 19343 15 = 8 ∧ acceleratedOrbit 15 19343 = 3874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19343) = 3 ^ 8 * m + 3874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19343.1, data_15_19343.2]

/-- Complete interval computation for depth 15, residue 19344. -/
theorem bounds_15_19344 : exactInterval 15 19344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19344 : oddCount 19344 15 = 7 ∧ acceleratedOrbit 15 19344 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19344) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19344.1, data_15_19344.2]

/-- Complete interval computation for depth 15, residue 19345. -/
theorem bounds_15_19345 : exactInterval 15 19345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19345 : oddCount 19345 15 = 6 ∧ acceleratedOrbit 15 19345 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19345) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19345.1, data_15_19345.2]

/-- Complete interval computation for depth 15, residue 19346. -/
theorem bounds_15_19346 : exactInterval 15 19346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19346 : oddCount 19346 15 = 6 ∧ acceleratedOrbit 15 19346 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19346) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19346.1, data_15_19346.2]

/-- Complete interval computation for depth 15, residue 19347. -/
theorem bounds_15_19347 : exactInterval 15 19347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19347 : oddCount 19347 15 = 6 ∧ acceleratedOrbit 15 19347 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19347) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19347.1, data_15_19347.2]

/-- Complete interval computation for depth 15, residue 19348. -/
theorem bounds_15_19348 : exactInterval 15 19348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19348 : oddCount 19348 15 = 7 ∧ acceleratedOrbit 15 19348 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19348) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19348.1, data_15_19348.2]

/-- Complete interval computation for depth 15, residue 19349. -/
theorem bounds_15_19349 : exactInterval 15 19349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19349 : oddCount 19349 15 = 7 ∧ acceleratedOrbit 15 19349 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19349) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19349.1, data_15_19349.2]

/-- Complete interval computation for depth 15, residue 19350. -/
theorem bounds_15_19350 : exactInterval 15 19350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19350 : oddCount 19350 15 = 8 ∧ acceleratedOrbit 15 19350 = 3878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19350) = 3 ^ 8 * m + 3878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19350.1, data_15_19350.2]

/-- Complete interval computation for depth 15, residue 19351. -/
theorem bounds_15_19351 : exactInterval 15 19351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19351 : oddCount 19351 15 = 8 ∧ acceleratedOrbit 15 19351 = 3878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19351) = 3 ^ 8 * m + 3878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19351.1, data_15_19351.2]

/-- Complete interval computation for depth 15, residue 19352. -/
theorem bounds_15_19352 : exactInterval 15 19352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19352 : oddCount 19352 15 = 7 ∧ acceleratedOrbit 15 19352 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19352) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19352.1, data_15_19352.2]

/-- Complete interval computation for depth 15, residue 19353. -/
theorem bounds_15_19353 : exactInterval 15 19353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19353 : oddCount 19353 15 = 8 ∧ acceleratedOrbit 15 19353 = 3878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19353) = 3 ^ 8 * m + 3878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19353.1, data_15_19353.2]

/-- Complete interval computation for depth 15, residue 19354. -/
theorem bounds_15_19354 : exactInterval 15 19354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19354 : oddCount 19354 15 = 7 ∧ acceleratedOrbit 15 19354 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19354) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19354.1, data_15_19354.2]

/-- Complete interval computation for depth 15, residue 19355. -/
theorem bounds_15_19355 : exactInterval 15 19355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19355 : oddCount 19355 15 = 7 ∧ acceleratedOrbit 15 19355 = 1292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19355) = 3 ^ 7 * m + 1292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19355.1, data_15_19355.2]

/-- Complete interval computation for depth 15, residue 19356. -/
theorem bounds_15_19356 : exactInterval 15 19356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19356 : oddCount 19356 15 = 9 ∧ acceleratedOrbit 15 19356 = 11630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19356) = 3 ^ 9 * m + 11630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19356.1, data_15_19356.2]

/-- Complete interval computation for depth 15, residue 19357. -/
theorem bounds_15_19357 : exactInterval 15 19357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19357 : oddCount 19357 15 = 9 ∧ acceleratedOrbit 15 19357 = 11630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19357) = 3 ^ 9 * m + 11630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19357.1, data_15_19357.2]

/-- Complete interval computation for depth 15, residue 19358. -/
theorem bounds_15_19358 : exactInterval 15 19358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19358 : oddCount 19358 15 = 9 ∧ acceleratedOrbit 15 19358 = 11630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19358) = 3 ^ 9 * m + 11630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19358.1, data_15_19358.2]

/-- Complete interval computation for depth 15, residue 19359. -/
theorem bounds_15_19359 : exactInterval 15 19359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19359 : oddCount 19359 15 = 9 ∧ acceleratedOrbit 15 19359 = 11630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19359) = 3 ^ 9 * m + 11630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19359.1, data_15_19359.2]

/-- Complete interval computation for depth 15, residue 19360. -/
theorem bounds_15_19360 : exactInterval 15 19360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19360 : oddCount 19360 15 = 3 ∧ acceleratedOrbit 15 19360 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19360) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19360.1, data_15_19360.2]

/-- Complete interval computation for depth 15, residue 19361. -/
theorem bounds_15_19361 : exactInterval 15 19361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19361 : oddCount 19361 15 = 8 ∧ acceleratedOrbit 15 19361 = 3878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19361) = 3 ^ 8 * m + 3878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19361.1, data_15_19361.2]

/-- Complete interval computation for depth 15, residue 19362. -/
theorem bounds_15_19362 : exactInterval 15 19362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19362 : oddCount 19362 15 = 7 ∧ acceleratedOrbit 15 19362 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19362) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19362.1, data_15_19362.2]

/-- Complete interval computation for depth 15, residue 19363. -/
theorem bounds_15_19363 : exactInterval 15 19363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19363 : oddCount 19363 15 = 7 ∧ acceleratedOrbit 15 19363 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19363) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19363.1, data_15_19363.2]

/-- Complete interval computation for depth 15, residue 19364. -/
theorem bounds_15_19364 : exactInterval 15 19364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19364 : oddCount 19364 15 = 10 ∧ acceleratedOrbit 15 19364 = 34910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19364) = 3 ^ 10 * m + 34910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19364.1, data_15_19364.2]

end Collatz.Research.PassageAtlas.Batch0591
