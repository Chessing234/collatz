import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0194

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6324. -/
theorem bounds_15_6324 : exactInterval 15 6324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6324 : oddCount 6324 15 = 7 ∧ acceleratedOrbit 15 6324 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6324) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6324.1, data_15_6324.2]

/-- Complete interval computation for depth 15, residue 6325. -/
theorem bounds_15_6325 : exactInterval 15 6325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6325 : oddCount 6325 15 = 7 ∧ acceleratedOrbit 15 6325 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6325) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6325.1, data_15_6325.2]

/-- Complete interval computation for depth 15, residue 6326. -/
theorem bounds_15_6326 : exactInterval 15 6326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6326 : oddCount 6326 15 = 9 ∧ acceleratedOrbit 15 6326 = 3802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6326) = 3 ^ 9 * m + 3802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6326.1, data_15_6326.2]

/-- Complete interval computation for depth 15, residue 6327. -/
theorem bounds_15_6327 : exactInterval 15 6327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6327 : oddCount 6327 15 = 9 ∧ acceleratedOrbit 15 6327 = 3802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6327) = 3 ^ 9 * m + 3802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6327.1, data_15_6327.2]

/-- Complete interval computation for depth 15, residue 6328. -/
theorem bounds_15_6328 : exactInterval 15 6328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6328 : oddCount 6328 15 = 7 ∧ acceleratedOrbit 15 6328 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6328) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6328.1, data_15_6328.2]

/-- Complete interval computation for depth 15, residue 6329. -/
theorem bounds_15_6329 : exactInterval 15 6329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6329 : oddCount 6329 15 = 9 ∧ acceleratedOrbit 15 6329 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6329) = 3 ^ 9 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6329.1, data_15_6329.2]

/-- Complete interval computation for depth 15, residue 6330. -/
theorem bounds_15_6330 : exactInterval 15 6330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6330 : oddCount 6330 15 = 7 ∧ acceleratedOrbit 15 6330 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6330) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6330.1, data_15_6330.2]

/-- Complete interval computation for depth 15, residue 6331. -/
theorem bounds_15_6331 : exactInterval 15 6331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6331 : oddCount 6331 15 = 10 ∧ acceleratedOrbit 15 6331 = 11414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6331) = 3 ^ 10 * m + 11414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6331.1, data_15_6331.2]

/-- Complete interval computation for depth 15, residue 6332. -/
theorem bounds_15_6332 : exactInterval 15 6332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6332 : oddCount 6332 15 = 11 ∧ acceleratedOrbit 15 6332 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6332) = 3 ^ 11 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6332.1, data_15_6332.2]

/-- Complete interval computation for depth 15, residue 6333. -/
theorem bounds_15_6333 : exactInterval 15 6333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6333 : oddCount 6333 15 = 11 ∧ acceleratedOrbit 15 6333 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6333) = 3 ^ 11 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6333.1, data_15_6333.2]

/-- Complete interval computation for depth 15, residue 6334. -/
theorem bounds_15_6334 : exactInterval 15 6334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6334 : oddCount 6334 15 = 11 ∧ acceleratedOrbit 15 6334 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6334) = 3 ^ 11 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6334.1, data_15_6334.2]

/-- Complete interval computation for depth 15, residue 6335. -/
theorem bounds_15_6335 : exactInterval 15 6335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6335 : oddCount 6335 15 = 10 ∧ acceleratedOrbit 15 6335 = 11420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6335) = 3 ^ 10 * m + 11420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6335.1, data_15_6335.2]

/-- Complete interval computation for depth 15, residue 6336. -/
theorem bounds_15_6336 : exactInterval 15 6336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6336 : oddCount 6336 15 = 4 ∧ acceleratedOrbit 15 6336 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6336) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6336.1, data_15_6336.2]

/-- Complete interval computation for depth 15, residue 6337. -/
theorem bounds_15_6337 : exactInterval 15 6337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6337 : oddCount 6337 15 = 8 ∧ acceleratedOrbit 15 6337 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6337) = 3 ^ 8 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6337.1, data_15_6337.2]

/-- Complete interval computation for depth 15, residue 6338. -/
theorem bounds_15_6338 : exactInterval 15 6338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6338 : oddCount 6338 15 = 8 ∧ acceleratedOrbit 15 6338 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6338) = 3 ^ 8 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6338.1, data_15_6338.2]

/-- Complete interval computation for depth 15, residue 6339. -/
theorem bounds_15_6339 : exactInterval 15 6339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6339 : oddCount 6339 15 = 8 ∧ acceleratedOrbit 15 6339 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6339) = 3 ^ 8 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6339.1, data_15_6339.2]

/-- Complete interval computation for depth 15, residue 6340. -/
theorem bounds_15_6340 : exactInterval 15 6340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6340 : oddCount 6340 15 = 7 ∧ acceleratedOrbit 15 6340 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6340) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6340.1, data_15_6340.2]

/-- Complete interval computation for depth 15, residue 6341. -/
theorem bounds_15_6341 : exactInterval 15 6341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6341 : oddCount 6341 15 = 7 ∧ acceleratedOrbit 15 6341 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6341) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6341.1, data_15_6341.2]

/-- Complete interval computation for depth 15, residue 6342. -/
theorem bounds_15_6342 : exactInterval 15 6342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6342 : oddCount 6342 15 = 7 ∧ acceleratedOrbit 15 6342 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6342) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6342.1, data_15_6342.2]

/-- Complete interval computation for depth 15, residue 6343. -/
theorem bounds_15_6343 : exactInterval 15 6343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6343 : oddCount 6343 15 = 8 ∧ acceleratedOrbit 15 6343 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6343) = 3 ^ 8 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6343.1, data_15_6343.2]

/-- Complete interval computation for depth 15, residue 6344. -/
theorem bounds_15_6344 : exactInterval 15 6344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6344 : oddCount 6344 15 = 7 ∧ acceleratedOrbit 15 6344 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6344) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6344.1, data_15_6344.2]

/-- Complete interval computation for depth 15, residue 6345. -/
theorem bounds_15_6345 : exactInterval 15 6345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6345 : oddCount 6345 15 = 7 ∧ acceleratedOrbit 15 6345 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6345) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6345.1, data_15_6345.2]

/-- Complete interval computation for depth 15, residue 6346. -/
theorem bounds_15_6346 : exactInterval 15 6346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6346 : oddCount 6346 15 = 7 ∧ acceleratedOrbit 15 6346 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6346) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6346.1, data_15_6346.2]

/-- Complete interval computation for depth 15, residue 6347. -/
theorem bounds_15_6347 : exactInterval 15 6347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6347 : oddCount 6347 15 = 7 ∧ acceleratedOrbit 15 6347 = 424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6347) = 3 ^ 7 * m + 424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6347.1, data_15_6347.2]

/-- Complete interval computation for depth 15, residue 6348. -/
theorem bounds_15_6348 : exactInterval 15 6348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6348 : oddCount 6348 15 = 7 ∧ acceleratedOrbit 15 6348 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6348) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6348.1, data_15_6348.2]

/-- Complete interval computation for depth 15, residue 6349. -/
theorem bounds_15_6349 : exactInterval 15 6349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6349 : oddCount 6349 15 = 7 ∧ acceleratedOrbit 15 6349 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6349) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6349.1, data_15_6349.2]

/-- Complete interval computation for depth 15, residue 6350. -/
theorem bounds_15_6350 : exactInterval 15 6350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6350 : oddCount 6350 15 = 12 ∧ acceleratedOrbit 15 6350 = 103031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6350) = 3 ^ 12 * m + 103031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6350.1, data_15_6350.2]

/-- Complete interval computation for depth 15, residue 6351. -/
theorem bounds_15_6351 : exactInterval 15 6351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6351 : oddCount 6351 15 = 12 ∧ acceleratedOrbit 15 6351 = 103031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6351) = 3 ^ 12 * m + 103031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6351.1, data_15_6351.2]

/-- Complete interval computation for depth 15, residue 6352. -/
theorem bounds_15_6352 : exactInterval 15 6352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6352 : oddCount 6352 15 = 4 ∧ acceleratedOrbit 15 6352 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6352) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6352.1, data_15_6352.2]

/-- Complete interval computation for depth 15, residue 6353. -/
theorem bounds_15_6353 : exactInterval 15 6353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6353 : oddCount 6353 15 = 9 ∧ acceleratedOrbit 15 6353 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6353) = 3 ^ 9 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6353.1, data_15_6353.2]

/-- Complete interval computation for depth 15, residue 6354. -/
theorem bounds_15_6354 : exactInterval 15 6354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6354 : oddCount 6354 15 = 9 ∧ acceleratedOrbit 15 6354 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6354) = 3 ^ 9 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6354.1, data_15_6354.2]

/-- Complete interval computation for depth 15, residue 6355. -/
theorem bounds_15_6355 : exactInterval 15 6355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6355 : oddCount 6355 15 = 9 ∧ acceleratedOrbit 15 6355 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6355) = 3 ^ 9 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6355.1, data_15_6355.2]

end Collatz.Research.PassageAtlas.Batch0194
