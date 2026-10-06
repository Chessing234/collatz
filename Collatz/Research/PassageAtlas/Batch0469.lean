import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0469

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15335. -/
theorem bounds_15_15335 : exactInterval 15 15335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15335 : oddCount 15335 15 = 8 ∧ acceleratedOrbit 15 15335 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15335) = 3 ^ 8 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15335.1, data_15_15335.2]

/-- Complete interval computation for depth 15, residue 15336. -/
theorem bounds_15_15336 : exactInterval 15 15336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15336 : oddCount 15336 15 = 8 ∧ acceleratedOrbit 15 15336 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15336) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15336.1, data_15_15336.2]

/-- Complete interval computation for depth 15, residue 15337. -/
theorem bounds_15_15337 : exactInterval 15 15337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15337 : oddCount 15337 15 = 12 ∧ acceleratedOrbit 15 15337 = 248771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15337) = 3 ^ 12 * m + 248771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15337.1, data_15_15337.2]

/-- Complete interval computation for depth 15, residue 15338. -/
theorem bounds_15_15338 : exactInterval 15 15338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15338 : oddCount 15338 15 = 8 ∧ acceleratedOrbit 15 15338 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15338) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15338.1, data_15_15338.2]

/-- Complete interval computation for depth 15, residue 15339. -/
theorem bounds_15_15339 : exactInterval 15 15339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15339 : oddCount 15339 15 = 10 ∧ acceleratedOrbit 15 15339 = 27647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15339) = 3 ^ 10 * m + 27647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15339.1, data_15_15339.2]

/-- Complete interval computation for depth 15, residue 15340. -/
theorem bounds_15_15340 : exactInterval 15 15340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15340 : oddCount 15340 15 = 8 ∧ acceleratedOrbit 15 15340 = 3073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15340) = 3 ^ 8 * m + 3073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15340.1, data_15_15340.2]

/-- Complete interval computation for depth 15, residue 15341. -/
theorem bounds_15_15341 : exactInterval 15 15341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15341 : oddCount 15341 15 = 8 ∧ acceleratedOrbit 15 15341 = 3073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15341) = 3 ^ 8 * m + 3073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15341.1, data_15_15341.2]

/-- Complete interval computation for depth 15, residue 15342. -/
theorem bounds_15_15342 : exactInterval 15 15342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15342 : oddCount 15342 15 = 8 ∧ acceleratedOrbit 15 15342 = 3073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15342) = 3 ^ 8 * m + 3073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15342.1, data_15_15342.2]

/-- Complete interval computation for depth 15, residue 15343. -/
theorem bounds_15_15343 : exactInterval 15 15343 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15343) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15343 : oddCount 15343 15 = 9 ∧ acceleratedOrbit 15 15343 = 9217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15343) = 3 ^ 9 * m + 9217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15343.1, data_15_15343.2]

/-- Complete interval computation for depth 15, residue 15344. -/
theorem bounds_15_15344 : exactInterval 15 15344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15344 : oddCount 15344 15 = 9 ∧ acceleratedOrbit 15 15344 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15344) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15344.1, data_15_15344.2]

/-- Complete interval computation for depth 15, residue 15345. -/
theorem bounds_15_15345 : exactInterval 15 15345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15345 : oddCount 15345 15 = 8 ∧ acceleratedOrbit 15 15345 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15345) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15345.1, data_15_15345.2]

/-- Complete interval computation for depth 15, residue 15346. -/
theorem bounds_15_15346 : exactInterval 15 15346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15346 : oddCount 15346 15 = 7 ∧ acceleratedOrbit 15 15346 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15346) = 3 ^ 7 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15346.1, data_15_15346.2]

/-- Complete interval computation for depth 15, residue 15347. -/
theorem bounds_15_15347 : exactInterval 15 15347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15347 : oddCount 15347 15 = 7 ∧ acceleratedOrbit 15 15347 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15347) = 3 ^ 7 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15347.1, data_15_15347.2]

/-- Complete interval computation for depth 15, residue 15348. -/
theorem bounds_15_15348 : exactInterval 15 15348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15348 : oddCount 15348 15 = 9 ∧ acceleratedOrbit 15 15348 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15348) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15348.1, data_15_15348.2]

/-- Complete interval computation for depth 15, residue 15349. -/
theorem bounds_15_15349 : exactInterval 15 15349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15349 : oddCount 15349 15 = 9 ∧ acceleratedOrbit 15 15349 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15349) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15349.1, data_15_15349.2]

/-- Complete interval computation for depth 15, residue 15350. -/
theorem bounds_15_15350 : exactInterval 15 15350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15350 : oddCount 15350 15 = 9 ∧ acceleratedOrbit 15 15350 = 9224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15350) = 3 ^ 9 * m + 9224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15350.1, data_15_15350.2]

/-- Complete interval computation for depth 15, residue 15351. -/
theorem bounds_15_15351 : exactInterval 15 15351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15351 : oddCount 15351 15 = 9 ∧ acceleratedOrbit 15 15351 = 9224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15351) = 3 ^ 9 * m + 9224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15351.1, data_15_15351.2]

/-- Complete interval computation for depth 15, residue 15352. -/
theorem bounds_15_15352 : exactInterval 15 15352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15352 : oddCount 15352 15 = 9 ∧ acceleratedOrbit 15 15352 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15352) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15352.1, data_15_15352.2]

/-- Complete interval computation for depth 15, residue 15353. -/
theorem bounds_15_15353 : exactInterval 15 15353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15353 : oddCount 15353 15 = 11 ∧ acceleratedOrbit 15 15353 = 83015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15353) = 3 ^ 11 * m + 83015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15353.1, data_15_15353.2]

/-- Complete interval computation for depth 15, residue 15354. -/
theorem bounds_15_15354 : exactInterval 15 15354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15354 : oddCount 15354 15 = 9 ∧ acceleratedOrbit 15 15354 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15354) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15354.1, data_15_15354.2]

/-- Complete interval computation for depth 15, residue 15355. -/
theorem bounds_15_15355 : exactInterval 15 15355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15355 : oddCount 15355 15 = 11 ∧ acceleratedOrbit 15 15355 = 83024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15355) = 3 ^ 11 * m + 83024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15355.1, data_15_15355.2]

/-- Complete interval computation for depth 15, residue 15356. -/
theorem bounds_15_15356 : exactInterval 15 15356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15356 : oddCount 15356 15 = 11 ∧ acceleratedOrbit 15 15356 = 83038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15356) = 3 ^ 11 * m + 83038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15356.1, data_15_15356.2]

/-- Complete interval computation for depth 15, residue 15357. -/
theorem bounds_15_15357 : exactInterval 15 15357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15357 : oddCount 15357 15 = 11 ∧ acceleratedOrbit 15 15357 = 83038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15357) = 3 ^ 11 * m + 83038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15357.1, data_15_15357.2]

/-- Complete interval computation for depth 15, residue 15358. -/
theorem bounds_15_15358 : exactInterval 15 15358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15358 : oddCount 15358 15 = 11 ∧ acceleratedOrbit 15 15358 = 83038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15358) = 3 ^ 11 * m + 83038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15358.1, data_15_15358.2]

/-- Complete interval computation for depth 15, residue 15359. -/
theorem bounds_15_15359 : exactInterval 15 15359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15359 : oddCount 15359 15 = 12 ∧ acceleratedOrbit 15 15359 = 249113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15359) = 3 ^ 12 * m + 249113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15359.1, data_15_15359.2]

/-- Complete interval computation for depth 15, residue 15360. -/
theorem bounds_15_15360 : exactInterval 15 15360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15360 : oddCount 15360 15 = 4 ∧ acceleratedOrbit 15 15360 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15360) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15360.1, data_15_15360.2]

/-- Complete interval computation for depth 15, residue 15361. -/
theorem bounds_15_15361 : exactInterval 15 15361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15361 : oddCount 15361 15 = 9 ∧ acceleratedOrbit 15 15361 = 9233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15361) = 3 ^ 9 * m + 9233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15361.1, data_15_15361.2]

/-- Complete interval computation for depth 15, residue 15362. -/
theorem bounds_15_15362 : exactInterval 15 15362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15362 : oddCount 15362 15 = 10 ∧ acceleratedOrbit 15 15362 = 27701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15362) = 3 ^ 10 * m + 27701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15362.1, data_15_15362.2]

/-- Complete interval computation for depth 15, residue 15363. -/
theorem bounds_15_15363 : exactInterval 15 15363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15363 : oddCount 15363 15 = 10 ∧ acceleratedOrbit 15 15363 = 27701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15363) = 3 ^ 10 * m + 27701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15363.1, data_15_15363.2]

/-- Complete interval computation for depth 15, residue 15364. -/
theorem bounds_15_15364 : exactInterval 15 15364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15364 : oddCount 15364 15 = 4 ∧ acceleratedOrbit 15 15364 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15364) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15364.1, data_15_15364.2]

/-- Complete interval computation for depth 15, residue 15365. -/
theorem bounds_15_15365 : exactInterval 15 15365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15365 : oddCount 15365 15 = 4 ∧ acceleratedOrbit 15 15365 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15365) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15365.1, data_15_15365.2]

/-- Complete interval computation for depth 15, residue 15366. -/
theorem bounds_15_15366 : exactInterval 15 15366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15366 : oddCount 15366 15 = 4 ∧ acceleratedOrbit 15 15366 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15366) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15366.1, data_15_15366.2]

/-- Complete interval computation for depth 15, residue 15367. -/
theorem bounds_15_15367 : exactInterval 15 15367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15367 : oddCount 15367 15 = 10 ∧ acceleratedOrbit 15 15367 = 27701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15367) = 3 ^ 10 * m + 27701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15367.1, data_15_15367.2]

end Collatz.Research.PassageAtlas.Batch0469
