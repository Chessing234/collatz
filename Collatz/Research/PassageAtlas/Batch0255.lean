import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0255

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8323. -/
theorem bounds_15_8323 : exactInterval 15 8323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8323 : oddCount 8323 15 = 7 ∧ acceleratedOrbit 15 8323 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8323) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8323.1, data_15_8323.2]

/-- Complete interval computation for depth 15, residue 8324. -/
theorem bounds_15_8324 : exactInterval 15 8324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8324 : oddCount 8324 15 = 7 ∧ acceleratedOrbit 15 8324 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8324) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8324.1, data_15_8324.2]

/-- Complete interval computation for depth 15, residue 8325. -/
theorem bounds_15_8325 : exactInterval 15 8325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8325 : oddCount 8325 15 = 7 ∧ acceleratedOrbit 15 8325 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8325) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8325.1, data_15_8325.2]

/-- Complete interval computation for depth 15, residue 8326. -/
theorem bounds_15_8326 : exactInterval 15 8326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8326 : oddCount 8326 15 = 7 ∧ acceleratedOrbit 15 8326 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8326) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8326.1, data_15_8326.2]

/-- Complete interval computation for depth 15, residue 8327. -/
theorem bounds_15_8327 : exactInterval 15 8327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8327 : oddCount 8327 15 = 7 ∧ acceleratedOrbit 15 8327 = 556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8327) = 3 ^ 7 * m + 556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8327.1, data_15_8327.2]

/-- Complete interval computation for depth 15, residue 8328. -/
theorem bounds_15_8328 : exactInterval 15 8328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8328 : oddCount 8328 15 = 6 ∧ acceleratedOrbit 15 8328 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8328) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8328.1, data_15_8328.2]

/-- Complete interval computation for depth 15, residue 8329. -/
theorem bounds_15_8329 : exactInterval 15 8329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8329 : oddCount 8329 15 = 10 ∧ acceleratedOrbit 15 8329 = 15013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8329) = 3 ^ 10 * m + 15013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8329.1, data_15_8329.2]

/-- Complete interval computation for depth 15, residue 8330. -/
theorem bounds_15_8330 : exactInterval 15 8330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8330 : oddCount 8330 15 = 6 ∧ acceleratedOrbit 15 8330 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8330) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8330.1, data_15_8330.2]

/-- Complete interval computation for depth 15, residue 8331. -/
theorem bounds_15_8331 : exactInterval 15 8331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8331 : oddCount 8331 15 = 8 ∧ acceleratedOrbit 15 8331 = 1669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8331) = 3 ^ 8 * m + 1669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8331.1, data_15_8331.2]

/-- Complete interval computation for depth 15, residue 8332. -/
theorem bounds_15_8332 : exactInterval 15 8332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8332 : oddCount 8332 15 = 6 ∧ acceleratedOrbit 15 8332 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8332) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8332.1, data_15_8332.2]

/-- Complete interval computation for depth 15, residue 8333. -/
theorem bounds_15_8333 : exactInterval 15 8333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8333 : oddCount 8333 15 = 6 ∧ acceleratedOrbit 15 8333 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8333) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8333.1, data_15_8333.2]

/-- Complete interval computation for depth 15, residue 8334. -/
theorem bounds_15_8334 : exactInterval 15 8334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8334 : oddCount 8334 15 = 10 ∧ acceleratedOrbit 15 8334 = 15025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8334) = 3 ^ 10 * m + 15025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8334.1, data_15_8334.2]

/-- Complete interval computation for depth 15, residue 8335. -/
theorem bounds_15_8335 : exactInterval 15 8335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8335 : oddCount 8335 15 = 10 ∧ acceleratedOrbit 15 8335 = 15025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8335) = 3 ^ 10 * m + 15025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8335.1, data_15_8335.2]

/-- Complete interval computation for depth 15, residue 8336. -/
theorem bounds_15_8336 : exactInterval 15 8336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8336 : oddCount 8336 15 = 5 ∧ acceleratedOrbit 15 8336 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8336) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8336.1, data_15_8336.2]

/-- Complete interval computation for depth 15, residue 8337. -/
theorem bounds_15_8337 : exactInterval 15 8337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8337 : oddCount 8337 15 = 9 ∧ acceleratedOrbit 15 8337 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8337) = 3 ^ 9 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8337.1, data_15_8337.2]

/-- Complete interval computation for depth 15, residue 8338. -/
theorem bounds_15_8338 : exactInterval 15 8338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8338 : oddCount 8338 15 = 9 ∧ acceleratedOrbit 15 8338 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8338) = 3 ^ 9 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8338.1, data_15_8338.2]

/-- Complete interval computation for depth 15, residue 8339. -/
theorem bounds_15_8339 : exactInterval 15 8339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8339 : oddCount 8339 15 = 9 ∧ acceleratedOrbit 15 8339 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8339) = 3 ^ 9 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8339.1, data_15_8339.2]

/-- Complete interval computation for depth 15, residue 8340. -/
theorem bounds_15_8340 : exactInterval 15 8340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8340 : oddCount 8340 15 = 5 ∧ acceleratedOrbit 15 8340 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8340) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8340.1, data_15_8340.2]

/-- Complete interval computation for depth 15, residue 8341. -/
theorem bounds_15_8341 : exactInterval 15 8341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8341 : oddCount 8341 15 = 5 ∧ acceleratedOrbit 15 8341 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8341) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8341.1, data_15_8341.2]

/-- Complete interval computation for depth 15, residue 8342. -/
theorem bounds_15_8342 : exactInterval 15 8342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8342 : oddCount 8342 15 = 6 ∧ acceleratedOrbit 15 8342 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8342) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8342.1, data_15_8342.2]

/-- Complete interval computation for depth 15, residue 8343. -/
theorem bounds_15_8343 : exactInterval 15 8343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8343 : oddCount 8343 15 = 6 ∧ acceleratedOrbit 15 8343 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8343) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8343.1, data_15_8343.2]

/-- Complete interval computation for depth 15, residue 8344. -/
theorem bounds_15_8344 : exactInterval 15 8344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8344 : oddCount 8344 15 = 5 ∧ acceleratedOrbit 15 8344 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8344) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8344.1, data_15_8344.2]

/-- Complete interval computation for depth 15, residue 8345. -/
theorem bounds_15_8345 : exactInterval 15 8345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8345 : oddCount 8345 15 = 8 ∧ acceleratedOrbit 15 8345 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8345) = 3 ^ 8 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8345.1, data_15_8345.2]

/-- Complete interval computation for depth 15, residue 8346. -/
theorem bounds_15_8346 : exactInterval 15 8346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8346 : oddCount 8346 15 = 5 ∧ acceleratedOrbit 15 8346 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8346) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8346.1, data_15_8346.2]

/-- Complete interval computation for depth 15, residue 8347. -/
theorem bounds_15_8347 : exactInterval 15 8347 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8347) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8347 : oddCount 8347 15 = 9 ∧ acceleratedOrbit 15 8347 = 5015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8347) = 3 ^ 9 * m + 5015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8347.1, data_15_8347.2]

/-- Complete interval computation for depth 15, residue 8348. -/
theorem bounds_15_8348 : exactInterval 15 8348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8348 : oddCount 8348 15 = 9 ∧ acceleratedOrbit 15 8348 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8348) = 3 ^ 9 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8348.1, data_15_8348.2]

/-- Complete interval computation for depth 15, residue 8349. -/
theorem bounds_15_8349 : exactInterval 15 8349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8349 : oddCount 8349 15 = 9 ∧ acceleratedOrbit 15 8349 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8349) = 3 ^ 9 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8349.1, data_15_8349.2]

/-- Complete interval computation for depth 15, residue 8350. -/
theorem bounds_15_8350 : exactInterval 15 8350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8350 : oddCount 8350 15 = 9 ∧ acceleratedOrbit 15 8350 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8350) = 3 ^ 9 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8350.1, data_15_8350.2]

/-- Complete interval computation for depth 15, residue 8351. -/
theorem bounds_15_8351 : exactInterval 15 8351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8351 : oddCount 8351 15 = 12 ∧ acceleratedOrbit 15 8351 = 135458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8351) = 3 ^ 12 * m + 135458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8351.1, data_15_8351.2]

/-- Complete interval computation for depth 15, residue 8352. -/
theorem bounds_15_8352 : exactInterval 15 8352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8352 : oddCount 8352 15 = 3 ∧ acceleratedOrbit 15 8352 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8352) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8352.1, data_15_8352.2]

/-- Complete interval computation for depth 15, residue 8353. -/
theorem bounds_15_8353 : exactInterval 15 8353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8353 : oddCount 8353 15 = 10 ∧ acceleratedOrbit 15 8353 = 15059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8353) = 3 ^ 10 * m + 15059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8353.1, data_15_8353.2]

/-- Complete interval computation for depth 15, residue 8354. -/
theorem bounds_15_8354 : exactInterval 15 8354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8354 : oddCount 8354 15 = 5 ∧ acceleratedOrbit 15 8354 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8354) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8354.1, data_15_8354.2]

end Collatz.Research.PassageAtlas.Batch0255
