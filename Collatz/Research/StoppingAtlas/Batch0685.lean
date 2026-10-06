import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0685

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3338. -/
theorem bounds_13_3338 : exactInterval 13 3338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3338 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3338) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3338 : oddCount 3338 13 = 6 ∧ acceleratedOrbit 13 3338 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3338 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3338) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3338.1, data_13_3338.2]

/-- Complete interval computation for depth 13, residue 3339. -/
theorem bounds_13_3339 : exactInterval 13 3339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3339 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3339) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3339 : oddCount 3339 13 = 7 ∧ acceleratedOrbit 13 3339 = 893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3339 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3339) = 3 ^ 7 * m + 893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3339.1, data_13_3339.2]

/-- Complete interval computation for depth 13, residue 3340. -/
theorem bounds_13_3340 : exactInterval 13 3340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3340 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3340) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3340 : oddCount 3340 13 = 6 ∧ acceleratedOrbit 13 3340 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3340 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3340) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3340.1, data_13_3340.2]

/-- Complete interval computation for depth 13, residue 3341. -/
theorem bounds_13_3341 : exactInterval 13 3341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3341 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3341) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3341 : oddCount 3341 13 = 6 ∧ acceleratedOrbit 13 3341 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3341 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3341) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3341.1, data_13_3341.2]

/-- Complete interval computation for depth 13, residue 3342. -/
theorem bounds_13_3342 : exactInterval 13 3342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3342 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3342) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3342 : oddCount 3342 13 = 6 ∧ acceleratedOrbit 13 3342 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3342 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3342) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3342.1, data_13_3342.2]

/-- Complete interval computation for depth 13, residue 3343. -/
theorem bounds_13_3343 : exactInterval 13 3343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3343 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3343) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3343 : oddCount 3343 13 = 6 ∧ acceleratedOrbit 13 3343 = 298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3343 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3343) = 3 ^ 6 * m + 298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3343.1, data_13_3343.2]

/-- Complete interval computation for depth 13, residue 3344. -/
theorem bounds_13_3344 : exactInterval 13 3344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3344 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3344) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3344 : oddCount 3344 13 = 5 ∧ acceleratedOrbit 13 3344 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3344 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3344) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3344.1, data_13_3344.2]

/-- Complete interval computation for depth 13, residue 3345. -/
theorem bounds_13_3345 : exactInterval 13 3345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3345 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3345) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3345 : oddCount 3345 13 = 6 ∧ acceleratedOrbit 13 3345 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3345 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3345) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3345.1, data_13_3345.2]

/-- Complete interval computation for depth 13, residue 3346. -/
theorem bounds_13_3346 : exactInterval 13 3346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3346 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3346) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3346 : oddCount 3346 13 = 8 ∧ acceleratedOrbit 13 3346 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3346 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3346) = 3 ^ 8 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3346.1, data_13_3346.2]

/-- Complete interval computation for depth 13, residue 3347. -/
theorem bounds_13_3347 : exactInterval 13 3347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3347 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3347) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3347 : oddCount 3347 13 = 8 ∧ acceleratedOrbit 13 3347 = 2683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3347 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3347) = 3 ^ 8 * m + 2683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3347.1, data_13_3347.2]

/-- Complete interval computation for depth 13, residue 3348. -/
theorem bounds_13_3348 : exactInterval 13 3348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3348 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3348) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3348 : oddCount 3348 13 = 5 ∧ acceleratedOrbit 13 3348 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3348 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3348) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3348.1, data_13_3348.2]

/-- Complete interval computation for depth 13, residue 3349. -/
theorem bounds_13_3349 : exactInterval 13 3349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3349 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3349) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3349 : oddCount 3349 13 = 5 ∧ acceleratedOrbit 13 3349 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3349 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3349) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3349.1, data_13_3349.2]

/-- Complete interval computation for depth 13, residue 3350. -/
theorem bounds_13_3350 : exactInterval 13 3350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3350 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3350) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3350 : oddCount 3350 13 = 6 ∧ acceleratedOrbit 13 3350 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3350 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3350) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3350.1, data_13_3350.2]

/-- Complete interval computation for depth 13, residue 3351. -/
theorem bounds_13_3351 : exactInterval 13 3351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3351 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3351) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3351 : oddCount 3351 13 = 6 ∧ acceleratedOrbit 13 3351 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3351 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3351) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3351.1, data_13_3351.2]

/-- Complete interval computation for depth 13, residue 3352. -/
theorem bounds_13_3352 : exactInterval 13 3352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3352 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3352) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3352 : oddCount 3352 13 = 5 ∧ acceleratedOrbit 13 3352 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3352 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3352) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3352.1, data_13_3352.2]

end Collatz.Research.StoppingAtlas.Batch0685
