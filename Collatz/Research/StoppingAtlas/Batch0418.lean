import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0418

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3333. -/
theorem bounds_12_3333 : exactInterval 12 3333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3333 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3333) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3333 : oddCount 3333 12 = 3 ∧ acceleratedOrbit 12 3333 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3333 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3333) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3333.1, data_12_3333.2]

/-- Complete interval computation for depth 12, residue 3334. -/
theorem bounds_12_3334 : exactInterval 12 3334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3334 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3334) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3334 : oddCount 3334 12 = 3 ∧ acceleratedOrbit 12 3334 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3334 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3334) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3334.1, data_12_3334.2]

/-- Complete interval computation for depth 12, residue 3335. -/
theorem bounds_12_3335 : exactInterval 12 3335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3335 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3335) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3335 : oddCount 3335 12 = 9 ∧ acceleratedOrbit 12 3335 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3335 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3335) = 3 ^ 9 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3335.1, data_12_3335.2]

/-- Complete interval computation for depth 12, residue 3336. -/
theorem bounds_12_3336 : exactInterval 12 3336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3336 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3336) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3336 : oddCount 3336 12 = 5 ∧ acceleratedOrbit 12 3336 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3336 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3336) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3336.1, data_12_3336.2]

/-- Complete interval computation for depth 12, residue 3337. -/
theorem bounds_12_3337 : exactInterval 12 3337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3337 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3337) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3337 : oddCount 3337 12 = 7 ∧ acceleratedOrbit 12 3337 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3337 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3337) = 3 ^ 7 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3337.1, data_12_3337.2]

/-- Complete interval computation for depth 12, residue 3338. -/
theorem bounds_12_3338 : exactInterval 12 3338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3338 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3338) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3338 : oddCount 3338 12 = 5 ∧ acceleratedOrbit 12 3338 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3338 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3338) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3338.1, data_12_3338.2]

/-- Complete interval computation for depth 12, residue 3339. -/
theorem bounds_12_3339 : exactInterval 12 3339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3339 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3339) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3339 : oddCount 3339 12 = 6 ∧ acceleratedOrbit 12 3339 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3339 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3339) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3339.1, data_12_3339.2]

/-- Complete interval computation for depth 12, residue 3340. -/
theorem bounds_12_3340 : exactInterval 12 3340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3340 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3340) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3340 : oddCount 3340 12 = 5 ∧ acceleratedOrbit 12 3340 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3340 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3340) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3340.1, data_12_3340.2]

/-- Complete interval computation for depth 12, residue 3341. -/
theorem bounds_12_3341 : exactInterval 12 3341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3341 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3341) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3341 : oddCount 3341 12 = 5 ∧ acceleratedOrbit 12 3341 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3341 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3341) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3341.1, data_12_3341.2]

/-- Complete interval computation for depth 12, residue 3342. -/
theorem bounds_12_3342 : exactInterval 12 3342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3342 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3342) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3342 : oddCount 3342 12 = 6 ∧ acceleratedOrbit 12 3342 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3342 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3342) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3342.1, data_12_3342.2]

/-- Complete interval computation for depth 12, residue 3343. -/
theorem bounds_12_3343 : exactInterval 12 3343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3343 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3343) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3343 : oddCount 3343 12 = 6 ∧ acceleratedOrbit 12 3343 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3343 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3343) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3343.1, data_12_3343.2]

/-- Complete interval computation for depth 12, residue 3344. -/
theorem bounds_12_3344 : exactInterval 12 3344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3344 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3344) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3344 : oddCount 3344 12 = 4 ∧ acceleratedOrbit 12 3344 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3344 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3344) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3344.1, data_12_3344.2]

/-- Complete interval computation for depth 12, residue 3345. -/
theorem bounds_12_3345 : exactInterval 12 3345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3345 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3345) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3345 : oddCount 3345 12 = 5 ∧ acceleratedOrbit 12 3345 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3345 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3345) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3345.1, data_12_3345.2]

/-- Complete interval computation for depth 12, residue 3346. -/
theorem bounds_12_3346 : exactInterval 12 3346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3346 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3346) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3346 : oddCount 3346 12 = 8 ∧ acceleratedOrbit 12 3346 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3346 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3346) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3346.1, data_12_3346.2]

/-- Complete interval computation for depth 12, residue 3347. -/
theorem bounds_12_3347 : exactInterval 12 3347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3347 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3347) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3347 : oddCount 3347 12 = 8 ∧ acceleratedOrbit 12 3347 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3347 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3347) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3347.1, data_12_3347.2]

end Collatz.Research.StoppingAtlas.Batch0418
