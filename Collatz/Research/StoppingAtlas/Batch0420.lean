import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0420

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3363. -/
theorem bounds_12_3363 : exactInterval 12 3363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3363 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3363) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3363 : oddCount 3363 12 = 5 ∧ acceleratedOrbit 12 3363 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3363 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3363) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3363.1, data_12_3363.2]

/-- Complete interval computation for depth 12, residue 3364. -/
theorem bounds_12_3364 : exactInterval 12 3364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3364 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3364) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3364 : oddCount 3364 12 = 5 ∧ acceleratedOrbit 12 3364 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3364 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3364) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3364.1, data_12_3364.2]

/-- Complete interval computation for depth 12, residue 3365. -/
theorem bounds_12_3365 : exactInterval 12 3365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3365 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3365) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3365 : oddCount 3365 12 = 5 ∧ acceleratedOrbit 12 3365 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3365 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3365) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3365.1, data_12_3365.2]

/-- Complete interval computation for depth 12, residue 3366. -/
theorem bounds_12_3366 : exactInterval 12 3366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3366 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3366) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3366 : oddCount 3366 12 = 5 ∧ acceleratedOrbit 12 3366 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3366 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3366) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3366.1, data_12_3366.2]

/-- Complete interval computation for depth 12, residue 3367. -/
theorem bounds_12_3367 : exactInterval 12 3367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3367 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3367) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3367 : oddCount 3367 12 = 7 ∧ acceleratedOrbit 12 3367 = 1799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3367 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3367) = 3 ^ 7 * m + 1799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3367.1, data_12_3367.2]

/-- Complete interval computation for depth 12, residue 3368. -/
theorem bounds_12_3368 : exactInterval 12 3368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3368 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3368) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3368 : oddCount 3368 12 = 5 ∧ acceleratedOrbit 12 3368 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3368 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3368) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3368.1, data_12_3368.2]

/-- Complete interval computation for depth 12, residue 3369. -/
theorem bounds_12_3369 : exactInterval 12 3369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3369 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3369) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3369 : oddCount 3369 12 = 9 ∧ acceleratedOrbit 12 3369 = 16199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3369 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3369) = 3 ^ 9 * m + 16199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3369.1, data_12_3369.2]

/-- Complete interval computation for depth 12, residue 3370. -/
theorem bounds_12_3370 : exactInterval 12 3370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3370 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3370) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3370 : oddCount 3370 12 = 5 ∧ acceleratedOrbit 12 3370 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3370 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3370) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3370.1, data_12_3370.2]

/-- Complete interval computation for depth 12, residue 3371. -/
theorem bounds_12_3371 : exactInterval 12 3371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3371 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3371) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3371 : oddCount 3371 12 = 7 ∧ acceleratedOrbit 12 3371 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3371 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3371) = 3 ^ 7 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3371.1, data_12_3371.2]

/-- Complete interval computation for depth 12, residue 3372. -/
theorem bounds_12_3372 : exactInterval 12 3372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3372 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3372) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3372 : oddCount 3372 12 = 4 ∧ acceleratedOrbit 12 3372 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3372 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3372) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3372.1, data_12_3372.2]

/-- Complete interval computation for depth 12, residue 3373. -/
theorem bounds_12_3373 : exactInterval 12 3373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3373 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3373) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3373 : oddCount 3373 12 = 4 ∧ acceleratedOrbit 12 3373 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3373 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3373) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3373.1, data_12_3373.2]

/-- Complete interval computation for depth 12, residue 3374. -/
theorem bounds_12_3374 : exactInterval 12 3374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3374 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3374) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3374 : oddCount 3374 12 = 4 ∧ acceleratedOrbit 12 3374 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3374 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3374) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3374.1, data_12_3374.2]

/-- Complete interval computation for depth 12, residue 3375. -/
theorem bounds_12_3375 : exactInterval 12 3375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3375 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3375) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3375 : oddCount 3375 12 = 9 ∧ acceleratedOrbit 12 3375 = 16226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3375 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3375) = 3 ^ 9 * m + 16226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3375.1, data_12_3375.2]

/-- Complete interval computation for depth 12, residue 3376. -/
theorem bounds_12_3376 : exactInterval 12 3376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3376 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3376) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3376 : oddCount 3376 12 = 5 ∧ acceleratedOrbit 12 3376 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3376 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3376) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3376.1, data_12_3376.2]

/-- Complete interval computation for depth 12, residue 3377. -/
theorem bounds_12_3377 : exactInterval 12 3377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3377 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3377) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3377 : oddCount 3377 12 = 7 ∧ acceleratedOrbit 12 3377 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3377 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3377) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3377.1, data_12_3377.2]

/-- Complete interval computation for depth 12, residue 3378. -/
theorem bounds_12_3378 : exactInterval 12 3378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3378 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3378) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3378 : oddCount 3378 12 = 7 ∧ acceleratedOrbit 12 3378 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3378 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3378) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3378.1, data_12_3378.2]

end Collatz.Research.StoppingAtlas.Batch0420
