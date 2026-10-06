import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0774

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25329. -/
theorem bounds_15_25329 : exactInterval 15 25329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25329 : oddCount 25329 15 = 6 ∧ acceleratedOrbit 15 25329 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25329) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25329.1, data_15_25329.2]

/-- Complete interval computation for depth 15, residue 25330. -/
theorem bounds_15_25330 : exactInterval 15 25330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25330 : oddCount 25330 15 = 11 ∧ acceleratedOrbit 15 25330 = 136961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25330) = 3 ^ 11 * m + 136961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25330.1, data_15_25330.2]

/-- Complete interval computation for depth 15, residue 25331. -/
theorem bounds_15_25331 : exactInterval 15 25331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25331 : oddCount 25331 15 = 11 ∧ acceleratedOrbit 15 25331 = 136961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25331) = 3 ^ 11 * m + 136961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25331.1, data_15_25331.2]

/-- Complete interval computation for depth 15, residue 25332. -/
theorem bounds_15_25332 : exactInterval 15 25332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25332 : oddCount 25332 15 = 9 ∧ acceleratedOrbit 15 25332 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25332) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25332.1, data_15_25332.2]

/-- Complete interval computation for depth 15, residue 25333. -/
theorem bounds_15_25333 : exactInterval 15 25333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25333 : oddCount 25333 15 = 9 ∧ acceleratedOrbit 15 25333 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25333) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25333.1, data_15_25333.2]

/-- Complete interval computation for depth 15, residue 25334. -/
theorem bounds_15_25334 : exactInterval 15 25334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25334 : oddCount 25334 15 = 9 ∧ acceleratedOrbit 15 25334 = 15221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25334) = 3 ^ 9 * m + 15221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25334.1, data_15_25334.2]

/-- Complete interval computation for depth 15, residue 25335. -/
theorem bounds_15_25335 : exactInterval 15 25335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25335 : oddCount 25335 15 = 9 ∧ acceleratedOrbit 15 25335 = 15221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25335) = 3 ^ 9 * m + 15221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25335.1, data_15_25335.2]

/-- Complete interval computation for depth 15, residue 25336. -/
theorem bounds_15_25336 : exactInterval 15 25336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25336 : oddCount 25336 15 = 9 ∧ acceleratedOrbit 15 25336 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25336) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25336.1, data_15_25336.2]

/-- Complete interval computation for depth 15, residue 25337. -/
theorem bounds_15_25337 : exactInterval 15 25337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25337 : oddCount 25337 15 = 8 ∧ acceleratedOrbit 15 25337 = 5075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25337) = 3 ^ 8 * m + 5075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25337.1, data_15_25337.2]

/-- Complete interval computation for depth 15, residue 25338. -/
theorem bounds_15_25338 : exactInterval 15 25338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25338 : oddCount 25338 15 = 9 ∧ acceleratedOrbit 15 25338 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25338) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25338.1, data_15_25338.2]

/-- Complete interval computation for depth 15, residue 25339. -/
theorem bounds_15_25339 : exactInterval 15 25339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25339 : oddCount 25339 15 = 11 ∧ acceleratedOrbit 15 25339 = 136997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25339) = 3 ^ 11 * m + 136997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25339.1, data_15_25339.2]

/-- Complete interval computation for depth 15, residue 25340. -/
theorem bounds_15_25340 : exactInterval 15 25340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25340 : oddCount 25340 15 = 8 ∧ acceleratedOrbit 15 25340 = 5075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25340) = 3 ^ 8 * m + 5075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25340.1, data_15_25340.2]

/-- Complete interval computation for depth 15, residue 25341. -/
theorem bounds_15_25341 : exactInterval 15 25341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25341 : oddCount 25341 15 = 8 ∧ acceleratedOrbit 15 25341 = 5075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25341) = 3 ^ 8 * m + 5075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25341.1, data_15_25341.2]

/-- Complete interval computation for depth 15, residue 25342. -/
theorem bounds_15_25342 : exactInterval 15 25342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25342 : oddCount 25342 15 = 8 ∧ acceleratedOrbit 15 25342 = 5075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25342) = 3 ^ 8 * m + 5075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25342.1, data_15_25342.2]

/-- Complete interval computation for depth 15, residue 25343. -/
theorem bounds_15_25343 : exactInterval 15 25343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25343 : oddCount 25343 15 = 12 ∧ acceleratedOrbit 15 25343 = 411038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25343) = 3 ^ 12 * m + 411038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25343.1, data_15_25343.2]

/-- Complete interval computation for depth 15, residue 25344. -/
theorem bounds_15_25344 : exactInterval 15 25344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25344 : oddCount 25344 15 = 2 ∧ acceleratedOrbit 15 25344 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25344) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25344.1, data_15_25344.2]

/-- Complete interval computation for depth 15, residue 25345. -/
theorem bounds_15_25345 : exactInterval 15 25345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25345 : oddCount 25345 15 = 5 ∧ acceleratedOrbit 15 25345 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25345) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25345.1, data_15_25345.2]

/-- Complete interval computation for depth 15, residue 25346. -/
theorem bounds_15_25346 : exactInterval 15 25346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25346 : oddCount 25346 15 = 5 ∧ acceleratedOrbit 15 25346 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25346) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25346.1, data_15_25346.2]

/-- Complete interval computation for depth 15, residue 25347. -/
theorem bounds_15_25347 : exactInterval 15 25347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25347 : oddCount 25347 15 = 5 ∧ acceleratedOrbit 15 25347 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25347) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25347.1, data_15_25347.2]

/-- Complete interval computation for depth 15, residue 25348. -/
theorem bounds_15_25348 : exactInterval 15 25348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25348 : oddCount 25348 15 = 7 ∧ acceleratedOrbit 15 25348 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25348) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25348.1, data_15_25348.2]

/-- Complete interval computation for depth 15, residue 25349. -/
theorem bounds_15_25349 : exactInterval 15 25349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25349 : oddCount 25349 15 = 7 ∧ acceleratedOrbit 15 25349 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25349) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25349.1, data_15_25349.2]

/-- Complete interval computation for depth 15, residue 25350. -/
theorem bounds_15_25350 : exactInterval 15 25350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25350 : oddCount 25350 15 = 7 ∧ acceleratedOrbit 15 25350 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25350) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25350.1, data_15_25350.2]

/-- Complete interval computation for depth 15, residue 25351. -/
theorem bounds_15_25351 : exactInterval 15 25351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25351 : oddCount 25351 15 = 9 ∧ acceleratedOrbit 15 25351 = 15230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25351) = 3 ^ 9 * m + 15230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25351.1, data_15_25351.2]

/-- Complete interval computation for depth 15, residue 25352. -/
theorem bounds_15_25352 : exactInterval 15 25352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25352 : oddCount 25352 15 = 7 ∧ acceleratedOrbit 15 25352 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25352) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25352.1, data_15_25352.2]

/-- Complete interval computation for depth 15, residue 25353. -/
theorem bounds_15_25353 : exactInterval 15 25353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25353 : oddCount 25353 15 = 8 ∧ acceleratedOrbit 15 25353 = 5077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25353) = 3 ^ 8 * m + 5077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25353.1, data_15_25353.2]

/-- Complete interval computation for depth 15, residue 25354. -/
theorem bounds_15_25354 : exactInterval 15 25354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25354 : oddCount 25354 15 = 7 ∧ acceleratedOrbit 15 25354 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25354) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25354.1, data_15_25354.2]

/-- Complete interval computation for depth 15, residue 25355. -/
theorem bounds_15_25355 : exactInterval 15 25355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25355 : oddCount 25355 15 = 8 ∧ acceleratedOrbit 15 25355 = 5078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25355) = 3 ^ 8 * m + 5078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25355.1, data_15_25355.2]

/-- Complete interval computation for depth 15, residue 25356. -/
theorem bounds_15_25356 : exactInterval 15 25356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25356 : oddCount 25356 15 = 7 ∧ acceleratedOrbit 15 25356 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25356) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25356.1, data_15_25356.2]

/-- Complete interval computation for depth 15, residue 25357. -/
theorem bounds_15_25357 : exactInterval 15 25357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25357 : oddCount 25357 15 = 7 ∧ acceleratedOrbit 15 25357 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25357) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25357.1, data_15_25357.2]

/-- Complete interval computation for depth 15, residue 25358. -/
theorem bounds_15_25358 : exactInterval 15 25358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25358 : oddCount 25358 15 = 7 ∧ acceleratedOrbit 15 25358 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25358) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25358.1, data_15_25358.2]

/-- Complete interval computation for depth 15, residue 25359. -/
theorem bounds_15_25359 : exactInterval 15 25359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25359 : oddCount 25359 15 = 7 ∧ acceleratedOrbit 15 25359 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25359) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25359.1, data_15_25359.2]

/-- Complete interval computation for depth 15, residue 25360. -/
theorem bounds_15_25360 : exactInterval 15 25360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25360 : oddCount 25360 15 = 7 ∧ acceleratedOrbit 15 25360 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25360) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25360.1, data_15_25360.2]

/-- Complete interval computation for depth 15, residue 25361. -/
theorem bounds_15_25361 : exactInterval 15 25361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25361 : oddCount 25361 15 = 7 ∧ acceleratedOrbit 15 25361 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25361) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25361.1, data_15_25361.2]

end Collatz.Research.PassageAtlas.Batch0774
