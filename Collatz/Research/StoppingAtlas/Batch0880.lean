import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0880

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6333. -/
theorem bounds_13_6333 : exactInterval 13 6333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6333 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6333) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6333 : oddCount 6333 13 = 9 ∧ acceleratedOrbit 13 6333 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6333 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6333) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6333.1, data_13_6333.2]

/-- Complete interval computation for depth 13, residue 6334. -/
theorem bounds_13_6334 : exactInterval 13 6334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6334 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6334) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6334 : oddCount 6334 13 = 9 ∧ acceleratedOrbit 13 6334 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6334 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6334) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6334.1, data_13_6334.2]

/-- Complete interval computation for depth 13, residue 6335. -/
theorem bounds_13_6335 : exactInterval 13 6335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6335 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6335) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6335 : oddCount 6335 13 = 8 ∧ acceleratedOrbit 13 6335 = 5075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6335 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6335) = 3 ^ 8 * m + 5075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6335.1, data_13_6335.2]

/-- Complete interval computation for depth 13, residue 6336. -/
theorem bounds_13_6336 : exactInterval 13 6336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6336 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6336) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6336 : oddCount 6336 13 = 2 ∧ acceleratedOrbit 13 6336 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6336 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6336) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6336.1, data_13_6336.2]

/-- Complete interval computation for depth 13, residue 6337. -/
theorem bounds_13_6337 : exactInterval 13 6337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6337 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6337) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6337 : oddCount 6337 13 = 7 ∧ acceleratedOrbit 13 6337 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6337 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6337) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6337.1, data_13_6337.2]

/-- Complete interval computation for depth 13, residue 6338. -/
theorem bounds_13_6338 : exactInterval 13 6338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6338 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6338) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6338 : oddCount 6338 13 = 7 ∧ acceleratedOrbit 13 6338 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6338 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6338) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6338.1, data_13_6338.2]

/-- Complete interval computation for depth 13, residue 6339. -/
theorem bounds_13_6339 : exactInterval 13 6339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6339 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6339) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6339 : oddCount 6339 13 = 7 ∧ acceleratedOrbit 13 6339 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6339 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6339) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6339.1, data_13_6339.2]

/-- Complete interval computation for depth 13, residue 6340. -/
theorem bounds_13_6340 : exactInterval 13 6340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6340 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6340) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6340 : oddCount 6340 13 = 7 ∧ acceleratedOrbit 13 6340 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6340 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6340) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6340.1, data_13_6340.2]

/-- Complete interval computation for depth 13, residue 6341. -/
theorem bounds_13_6341 : exactInterval 13 6341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6341 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6341) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6341 : oddCount 6341 13 = 7 ∧ acceleratedOrbit 13 6341 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6341 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6341) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6341.1, data_13_6341.2]

/-- Complete interval computation for depth 13, residue 6342. -/
theorem bounds_13_6342 : exactInterval 13 6342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6342 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6342) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6342 : oddCount 6342 13 = 7 ∧ acceleratedOrbit 13 6342 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6342 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6342) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6342.1, data_13_6342.2]

/-- Complete interval computation for depth 13, residue 6343. -/
theorem bounds_13_6343 : exactInterval 13 6343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6343 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6343) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6343 : oddCount 6343 13 = 7 ∧ acceleratedOrbit 13 6343 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6343 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6343) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6343.1, data_13_6343.2]

/-- Complete interval computation for depth 13, residue 6344. -/
theorem bounds_13_6344 : exactInterval 13 6344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6344 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6344) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6344 : oddCount 6344 13 = 7 ∧ acceleratedOrbit 13 6344 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6344 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6344) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6344.1, data_13_6344.2]

/-- Complete interval computation for depth 13, residue 6345. -/
theorem bounds_13_6345 : exactInterval 13 6345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6345 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6345) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6345 : oddCount 6345 13 = 6 ∧ acceleratedOrbit 13 6345 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6345 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6345) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6345.1, data_13_6345.2]

/-- Complete interval computation for depth 13, residue 6346. -/
theorem bounds_13_6346 : exactInterval 13 6346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6346 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6346) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6346 : oddCount 6346 13 = 7 ∧ acceleratedOrbit 13 6346 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6346 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6346) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6346.1, data_13_6346.2]

/-- Complete interval computation for depth 13, residue 6347. -/
theorem bounds_13_6347 : exactInterval 13 6347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6347 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6347) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6347 : oddCount 6347 13 = 7 ∧ acceleratedOrbit 13 6347 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6347 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6347) = 3 ^ 7 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6347.1, data_13_6347.2]

end Collatz.Research.StoppingAtlas.Batch0880
