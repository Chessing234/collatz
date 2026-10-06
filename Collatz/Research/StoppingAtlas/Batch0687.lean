import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0687

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3368. -/
theorem bounds_13_3368 : exactInterval 13 3368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3368 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3368) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3368 : oddCount 3368 13 = 5 ∧ acceleratedOrbit 13 3368 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3368 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3368) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3368.1, data_13_3368.2]

/-- Complete interval computation for depth 13, residue 3369. -/
theorem bounds_13_3369 : exactInterval 13 3369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3369 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3369) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3369 : oddCount 3369 13 = 10 ∧ acceleratedOrbit 13 3369 = 24299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3369 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3369) = 3 ^ 10 * m + 24299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3369.1, data_13_3369.2]

/-- Complete interval computation for depth 13, residue 3370. -/
theorem bounds_13_3370 : exactInterval 13 3370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3370 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3370) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3370 : oddCount 3370 13 = 5 ∧ acceleratedOrbit 13 3370 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3370 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3370) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3370.1, data_13_3370.2]

/-- Complete interval computation for depth 13, residue 3371. -/
theorem bounds_13_3371 : exactInterval 13 3371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3371 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3371) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3371 : oddCount 3371 13 = 7 ∧ acceleratedOrbit 13 3371 = 901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3371 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3371) = 3 ^ 7 * m + 901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3371.1, data_13_3371.2]

/-- Complete interval computation for depth 13, residue 3372. -/
theorem bounds_13_3372 : exactInterval 13 3372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3372 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3372) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3372 : oddCount 3372 13 = 5 ∧ acceleratedOrbit 13 3372 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3372 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3372) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3372.1, data_13_3372.2]

/-- Complete interval computation for depth 13, residue 3373. -/
theorem bounds_13_3373 : exactInterval 13 3373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3373 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3373) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3373 : oddCount 3373 13 = 5 ∧ acceleratedOrbit 13 3373 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3373 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3373) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3373.1, data_13_3373.2]

/-- Complete interval computation for depth 13, residue 3374. -/
theorem bounds_13_3374 : exactInterval 13 3374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3374 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3374) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3374 : oddCount 3374 13 = 5 ∧ acceleratedOrbit 13 3374 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3374 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3374) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3374.1, data_13_3374.2]

/-- Complete interval computation for depth 13, residue 3375. -/
theorem bounds_13_3375 : exactInterval 13 3375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3375 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3375) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3375 : oddCount 3375 13 = 9 ∧ acceleratedOrbit 13 3375 = 8113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3375 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3375) = 3 ^ 9 * m + 8113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3375.1, data_13_3375.2]

/-- Complete interval computation for depth 13, residue 3376. -/
theorem bounds_13_3376 : exactInterval 13 3376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3376 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3376) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3376 : oddCount 3376 13 = 5 ∧ acceleratedOrbit 13 3376 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3376 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3376) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3376.1, data_13_3376.2]

/-- Complete interval computation for depth 13, residue 3377. -/
theorem bounds_13_3377 : exactInterval 13 3377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3377 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3377) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3377 : oddCount 3377 13 = 7 ∧ acceleratedOrbit 13 3377 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3377 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3377) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3377.1, data_13_3377.2]

/-- Complete interval computation for depth 13, residue 3378. -/
theorem bounds_13_3378 : exactInterval 13 3378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3378 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3378) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3378 : oddCount 3378 13 = 7 ∧ acceleratedOrbit 13 3378 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3378 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3378) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3378.1, data_13_3378.2]

/-- Complete interval computation for depth 13, residue 3379. -/
theorem bounds_13_3379 : exactInterval 13 3379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3379 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3379) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3379 : oddCount 3379 13 = 7 ∧ acceleratedOrbit 13 3379 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3379 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3379) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3379.1, data_13_3379.2]

/-- Complete interval computation for depth 13, residue 3380. -/
theorem bounds_13_3380 : exactInterval 13 3380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3380 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3380) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3380 : oddCount 3380 13 = 5 ∧ acceleratedOrbit 13 3380 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3380 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3380) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3380.1, data_13_3380.2]

/-- Complete interval computation for depth 13, residue 3381. -/
theorem bounds_13_3381 : exactInterval 13 3381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3381 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3381) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3381 : oddCount 3381 13 = 5 ∧ acceleratedOrbit 13 3381 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3381 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3381) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3381.1, data_13_3381.2]

/-- Complete interval computation for depth 13, residue 3382. -/
theorem bounds_13_3382 : exactInterval 13 3382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3382 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3382) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3382 : oddCount 3382 13 = 8 ∧ acceleratedOrbit 13 3382 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3382 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3382) = 3 ^ 8 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3382.1, data_13_3382.2]

/-- Complete interval computation for depth 13, residue 3383. -/
theorem bounds_13_3383 : exactInterval 13 3383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3383 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3383) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3383 : oddCount 3383 13 = 8 ∧ acceleratedOrbit 13 3383 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3383 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3383) = 3 ^ 8 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3383.1, data_13_3383.2]

end Collatz.Research.StoppingAtlas.Batch0687
