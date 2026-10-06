import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0896

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29327. -/
theorem bounds_15_29327 : exactInterval 15 29327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29327 : oddCount 29327 15 = 11 ∧ acceleratedOrbit 15 29327 = 158557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29327) = 3 ^ 11 * m + 158557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29327.1, data_15_29327.2]

/-- Complete interval computation for depth 15, residue 29328. -/
theorem bounds_15_29328 : exactInterval 15 29328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29328 : oddCount 29328 15 = 6 ∧ acceleratedOrbit 15 29328 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29328) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29328.1, data_15_29328.2]

/-- Complete interval computation for depth 15, residue 29329. -/
theorem bounds_15_29329 : exactInterval 15 29329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29329 : oddCount 29329 15 = 7 ∧ acceleratedOrbit 15 29329 = 1958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29329) = 3 ^ 7 * m + 1958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29329.1, data_15_29329.2]

/-- Complete interval computation for depth 15, residue 29330. -/
theorem bounds_15_29330 : exactInterval 15 29330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29330 : oddCount 29330 15 = 7 ∧ acceleratedOrbit 15 29330 = 1958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29330) = 3 ^ 7 * m + 1958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29330.1, data_15_29330.2]

/-- Complete interval computation for depth 15, residue 29331. -/
theorem bounds_15_29331 : exactInterval 15 29331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29331 : oddCount 29331 15 = 7 ∧ acceleratedOrbit 15 29331 = 1958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29331) = 3 ^ 7 * m + 1958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29331.1, data_15_29331.2]

/-- Complete interval computation for depth 15, residue 29332. -/
theorem bounds_15_29332 : exactInterval 15 29332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29332 : oddCount 29332 15 = 6 ∧ acceleratedOrbit 15 29332 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29332) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29332.1, data_15_29332.2]

/-- Complete interval computation for depth 15, residue 29333. -/
theorem bounds_15_29333 : exactInterval 15 29333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29333 : oddCount 29333 15 = 6 ∧ acceleratedOrbit 15 29333 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29333) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29333.1, data_15_29333.2]

/-- Complete interval computation for depth 15, residue 29334. -/
theorem bounds_15_29334 : exactInterval 15 29334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29334 : oddCount 29334 15 = 6 ∧ acceleratedOrbit 15 29334 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29334) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29334.1, data_15_29334.2]

/-- Complete interval computation for depth 15, residue 29335. -/
theorem bounds_15_29335 : exactInterval 15 29335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29335 : oddCount 29335 15 = 6 ∧ acceleratedOrbit 15 29335 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29335) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29335.1, data_15_29335.2]

/-- Complete interval computation for depth 15, residue 29336. -/
theorem bounds_15_29336 : exactInterval 15 29336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29336 : oddCount 29336 15 = 6 ∧ acceleratedOrbit 15 29336 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29336) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29336.1, data_15_29336.2]

/-- Complete interval computation for depth 15, residue 29337. -/
theorem bounds_15_29337 : exactInterval 15 29337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29337 : oddCount 29337 15 = 8 ∧ acceleratedOrbit 15 29337 = 5876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29337) = 3 ^ 8 * m + 5876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29337.1, data_15_29337.2]

/-- Complete interval computation for depth 15, residue 29338. -/
theorem bounds_15_29338 : exactInterval 15 29338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29338 : oddCount 29338 15 = 6 ∧ acceleratedOrbit 15 29338 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29338) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29338.1, data_15_29338.2]

/-- Complete interval computation for depth 15, residue 29339. -/
theorem bounds_15_29339 : exactInterval 15 29339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29339 : oddCount 29339 15 = 11 ∧ acceleratedOrbit 15 29339 = 158618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29339) = 3 ^ 11 * m + 158618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29339.1, data_15_29339.2]

/-- Complete interval computation for depth 15, residue 29340. -/
theorem bounds_15_29340 : exactInterval 15 29340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29340 : oddCount 29340 15 = 10 ∧ acceleratedOrbit 15 29340 = 52883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29340) = 3 ^ 10 * m + 52883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29340.1, data_15_29340.2]

/-- Complete interval computation for depth 15, residue 29341. -/
theorem bounds_15_29341 : exactInterval 15 29341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29341 : oddCount 29341 15 = 10 ∧ acceleratedOrbit 15 29341 = 52883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29341) = 3 ^ 10 * m + 52883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29341.1, data_15_29341.2]

/-- Complete interval computation for depth 15, residue 29342. -/
theorem bounds_15_29342 : exactInterval 15 29342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29342 : oddCount 29342 15 = 10 ∧ acceleratedOrbit 15 29342 = 52883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29342) = 3 ^ 10 * m + 52883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29342.1, data_15_29342.2]

/-- Complete interval computation for depth 15, residue 29343. -/
theorem bounds_15_29343 : exactInterval 15 29343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29343 : oddCount 29343 15 = 11 ∧ acceleratedOrbit 15 29343 = 158638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29343) = 3 ^ 11 * m + 158638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29343.1, data_15_29343.2]

/-- Complete interval computation for depth 15, residue 29344. -/
theorem bounds_15_29344 : exactInterval 15 29344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29344 : oddCount 29344 15 = 4 ∧ acceleratedOrbit 15 29344 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29344) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29344.1, data_15_29344.2]

/-- Complete interval computation for depth 15, residue 29345. -/
theorem bounds_15_29345 : exactInterval 15 29345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29345 : oddCount 29345 15 = 9 ∧ acceleratedOrbit 15 29345 = 17630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29345) = 3 ^ 9 * m + 17630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29345.1, data_15_29345.2]

/-- Complete interval computation for depth 15, residue 29346. -/
theorem bounds_15_29346 : exactInterval 15 29346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29346 : oddCount 29346 15 = 9 ∧ acceleratedOrbit 15 29346 = 17633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29346) = 3 ^ 9 * m + 17633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29346.1, data_15_29346.2]

/-- Complete interval computation for depth 15, residue 29347. -/
theorem bounds_15_29347 : exactInterval 15 29347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29347 : oddCount 29347 15 = 9 ∧ acceleratedOrbit 15 29347 = 17633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29347) = 3 ^ 9 * m + 17633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29347.1, data_15_29347.2]

/-- Complete interval computation for depth 15, residue 29348. -/
theorem bounds_15_29348 : exactInterval 15 29348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29348 : oddCount 29348 15 = 9 ∧ acceleratedOrbit 15 29348 = 17633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29348) = 3 ^ 9 * m + 17633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29348.1, data_15_29348.2]

/-- Complete interval computation for depth 15, residue 29349. -/
theorem bounds_15_29349 : exactInterval 15 29349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29349 : oddCount 29349 15 = 9 ∧ acceleratedOrbit 15 29349 = 17633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29349) = 3 ^ 9 * m + 17633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29349.1, data_15_29349.2]

/-- Complete interval computation for depth 15, residue 29350. -/
theorem bounds_15_29350 : exactInterval 15 29350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29350 : oddCount 29350 15 = 9 ∧ acceleratedOrbit 15 29350 = 17633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29350) = 3 ^ 9 * m + 17633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29350.1, data_15_29350.2]

/-- Complete interval computation for depth 15, residue 29351. -/
theorem bounds_15_29351 : exactInterval 15 29351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29351 : oddCount 29351 15 = 10 ∧ acceleratedOrbit 15 29351 = 52895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29351) = 3 ^ 10 * m + 52895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29351.1, data_15_29351.2]

/-- Complete interval computation for depth 15, residue 29352. -/
theorem bounds_15_29352 : exactInterval 15 29352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29352 : oddCount 29352 15 = 4 ∧ acceleratedOrbit 15 29352 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29352) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29352.1, data_15_29352.2]

/-- Complete interval computation for depth 15, residue 29353. -/
theorem bounds_15_29353 : exactInterval 15 29353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29353 : oddCount 29353 15 = 10 ∧ acceleratedOrbit 15 29353 = 52898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29353) = 3 ^ 10 * m + 52898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29353.1, data_15_29353.2]

/-- Complete interval computation for depth 15, residue 29354. -/
theorem bounds_15_29354 : exactInterval 15 29354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29354 : oddCount 29354 15 = 4 ∧ acceleratedOrbit 15 29354 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29354) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29354.1, data_15_29354.2]

/-- Complete interval computation for depth 15, residue 29355. -/
theorem bounds_15_29355 : exactInterval 15 29355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29355 : oddCount 29355 15 = 8 ∧ acceleratedOrbit 15 29355 = 5879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29355) = 3 ^ 8 * m + 5879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29355.1, data_15_29355.2]

/-- Complete interval computation for depth 15, residue 29356. -/
theorem bounds_15_29356 : exactInterval 15 29356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29356 : oddCount 29356 15 = 7 ∧ acceleratedOrbit 15 29356 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29356) = 3 ^ 7 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29356.1, data_15_29356.2]

/-- Complete interval computation for depth 15, residue 29357. -/
theorem bounds_15_29357 : exactInterval 15 29357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29357 : oddCount 29357 15 = 7 ∧ acceleratedOrbit 15 29357 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29357) = 3 ^ 7 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29357.1, data_15_29357.2]

/-- Complete interval computation for depth 15, residue 29358. -/
theorem bounds_15_29358 : exactInterval 15 29358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29358 : oddCount 29358 15 = 7 ∧ acceleratedOrbit 15 29358 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29358) = 3 ^ 7 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29358.1, data_15_29358.2]

/-- Complete interval computation for depth 15, residue 29359. -/
theorem bounds_15_29359 : exactInterval 15 29359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29359 : oddCount 29359 15 = 8 ∧ acceleratedOrbit 15 29359 = 5879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29359) = 3 ^ 8 * m + 5879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29359.1, data_15_29359.2]

end Collatz.Research.PassageAtlas.Batch0896
