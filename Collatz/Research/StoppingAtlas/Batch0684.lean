import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0684

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3322. -/
theorem bounds_13_3322 : exactInterval 13 3322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3322 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3322) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3322 : oddCount 3322 13 = 8 ∧ acceleratedOrbit 13 3322 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3322 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3322) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3322.1, data_13_3322.2]

/-- Complete interval computation for depth 13, residue 3323. -/
theorem bounds_13_3323 : exactInterval 13 3323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3323 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3323) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3323 : oddCount 3323 13 = 10 ∧ acceleratedOrbit 13 3323 = 23966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3323 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3323) = 3 ^ 10 * m + 23966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3323.1, data_13_3323.2]

/-- Complete interval computation for depth 13, residue 3324. -/
theorem bounds_13_3324 : exactInterval 13 3324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3324 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3324) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3324 : oddCount 3324 13 = 8 ∧ acceleratedOrbit 13 3324 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3324 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3324) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3324.1, data_13_3324.2]

/-- Complete interval computation for depth 13, residue 3325. -/
theorem bounds_13_3325 : exactInterval 13 3325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3325 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3325) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3325 : oddCount 3325 13 = 8 ∧ acceleratedOrbit 13 3325 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3325 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3325) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3325.1, data_13_3325.2]

/-- Complete interval computation for depth 13, residue 3326. -/
theorem bounds_13_3326 : exactInterval 13 3326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3326 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3326) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3326 : oddCount 3326 13 = 10 ∧ acceleratedOrbit 13 3326 = 23989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3326 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3326) = 3 ^ 10 * m + 23989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3326.1, data_13_3326.2]

/-- Complete interval computation for depth 13, residue 3327. -/
theorem bounds_13_3327 : exactInterval 13 3327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3327 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3327) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3327 : oddCount 3327 13 = 10 ∧ acceleratedOrbit 13 3327 = 23989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3327 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3327) = 3 ^ 10 * m + 23989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3327.1, data_13_3327.2]

/-- Complete interval computation for depth 13, residue 3328. -/
theorem bounds_13_3328 : exactInterval 13 3328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3328 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3328) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3328 : oddCount 3328 13 = 2 ∧ acceleratedOrbit 13 3328 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3328 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3328) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3328.1, data_13_3328.2]

/-- Complete interval computation for depth 13, residue 3329. -/
theorem bounds_13_3329 : exactInterval 13 3329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3329 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3329) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3329 : oddCount 3329 13 = 8 ∧ acceleratedOrbit 13 3329 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3329 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3329) = 3 ^ 8 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3329.1, data_13_3329.2]

/-- Complete interval computation for depth 13, residue 3330. -/
theorem bounds_13_3330 : exactInterval 13 3330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3330 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3330) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3330 : oddCount 3330 13 = 9 ∧ acceleratedOrbit 13 3330 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3330 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3330) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3330.1, data_13_3330.2]

/-- Complete interval computation for depth 13, residue 3331. -/
theorem bounds_13_3331 : exactInterval 13 3331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3331 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3331) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3331 : oddCount 3331 13 = 9 ∧ acceleratedOrbit 13 3331 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3331 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3331) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3331.1, data_13_3331.2]

/-- Complete interval computation for depth 13, residue 3332. -/
theorem bounds_13_3332 : exactInterval 13 3332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3332 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3332) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3332 : oddCount 3332 13 = 3 ∧ acceleratedOrbit 13 3332 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3332 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3332) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3332.1, data_13_3332.2]

/-- Complete interval computation for depth 13, residue 3333. -/
theorem bounds_13_3333 : exactInterval 13 3333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3333 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3333) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3333 : oddCount 3333 13 = 3 ∧ acceleratedOrbit 13 3333 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3333 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3333) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3333.1, data_13_3333.2]

/-- Complete interval computation for depth 13, residue 3334. -/
theorem bounds_13_3334 : exactInterval 13 3334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3334 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3334) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3334 : oddCount 3334 13 = 3 ∧ acceleratedOrbit 13 3334 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3334 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3334) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3334.1, data_13_3334.2]

/-- Complete interval computation for depth 13, residue 3335. -/
theorem bounds_13_3335 : exactInterval 13 3335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3335 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3335) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3335 : oddCount 3335 13 = 10 ∧ acceleratedOrbit 13 3335 = 24056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3335 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3335) = 3 ^ 10 * m + 24056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3335.1, data_13_3335.2]

/-- Complete interval computation for depth 13, residue 3336. -/
theorem bounds_13_3336 : exactInterval 13 3336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3336 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3336) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3336 : oddCount 3336 13 = 6 ∧ acceleratedOrbit 13 3336 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3336 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3336) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3336.1, data_13_3336.2]

/-- Complete interval computation for depth 13, residue 3337. -/
theorem bounds_13_3337 : exactInterval 13 3337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3337 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3337) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3337 : oddCount 3337 13 = 8 ∧ acceleratedOrbit 13 3337 = 2675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3337 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3337) = 3 ^ 8 * m + 2675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3337.1, data_13_3337.2]

end Collatz.Research.StoppingAtlas.Batch0684
