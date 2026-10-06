import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0417

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3317. -/
theorem bounds_12_3317 : exactInterval 12 3317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3317 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3317) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3317 : oddCount 3317 12 = 6 ∧ acceleratedOrbit 12 3317 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3317 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3317) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3317.1, data_12_3317.2]

/-- Complete interval computation for depth 12, residue 3318. -/
theorem bounds_12_3318 : exactInterval 12 3318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3318 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3318) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3318 : oddCount 3318 12 = 5 ∧ acceleratedOrbit 12 3318 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3318 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3318) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3318.1, data_12_3318.2]

/-- Complete interval computation for depth 12, residue 3319. -/
theorem bounds_12_3319 : exactInterval 12 3319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3319 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3319) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3319 : oddCount 3319 12 = 5 ∧ acceleratedOrbit 12 3319 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3319 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3319) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3319.1, data_12_3319.2]

/-- Complete interval computation for depth 12, residue 3320. -/
theorem bounds_12_3320 : exactInterval 12 3320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3320 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3320) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3320 : oddCount 3320 12 = 7 ∧ acceleratedOrbit 12 3320 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3320 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3320) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3320.1, data_12_3320.2]

/-- Complete interval computation for depth 12, residue 3321. -/
theorem bounds_12_3321 : exactInterval 12 3321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3321 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3321) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3321 : oddCount 3321 12 = 7 ∧ acceleratedOrbit 12 3321 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3321 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3321) = 3 ^ 7 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3321.1, data_12_3321.2]

/-- Complete interval computation for depth 12, residue 3322. -/
theorem bounds_12_3322 : exactInterval 12 3322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3322 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3322) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3322 : oddCount 3322 12 = 7 ∧ acceleratedOrbit 12 3322 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3322 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3322) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3322.1, data_12_3322.2]

/-- Complete interval computation for depth 12, residue 3323. -/
theorem bounds_12_3323 : exactInterval 12 3323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3323 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3323) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3323 : oddCount 3323 12 = 9 ∧ acceleratedOrbit 12 3323 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3323 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3323) = 3 ^ 9 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3323.1, data_12_3323.2]

/-- Complete interval computation for depth 12, residue 3324. -/
theorem bounds_12_3324 : exactInterval 12 3324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3324 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3324) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3324 : oddCount 3324 12 = 7 ∧ acceleratedOrbit 12 3324 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3324 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3324) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3324.1, data_12_3324.2]

/-- Complete interval computation for depth 12, residue 3325. -/
theorem bounds_12_3325 : exactInterval 12 3325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3325 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3325) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3325 : oddCount 3325 12 = 7 ∧ acceleratedOrbit 12 3325 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3325 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3325) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3325.1, data_12_3325.2]

/-- Complete interval computation for depth 12, residue 3326. -/
theorem bounds_12_3326 : exactInterval 12 3326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3326 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3326) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3326 : oddCount 3326 12 = 10 ∧ acceleratedOrbit 12 3326 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3326 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3326) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3326.1, data_12_3326.2]

/-- Complete interval computation for depth 12, residue 3327. -/
theorem bounds_12_3327 : exactInterval 12 3327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3327 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3327) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3327 : oddCount 3327 12 = 10 ∧ acceleratedOrbit 12 3327 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3327 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3327) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3327.1, data_12_3327.2]

/-- Complete interval computation for depth 12, residue 3328. -/
theorem bounds_12_3328 : exactInterval 12 3328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3328 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3328) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3328 : oddCount 3328 12 = 2 ∧ acceleratedOrbit 12 3328 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3328 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3328) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3328.1, data_12_3328.2]

/-- Complete interval computation for depth 12, residue 3329. -/
theorem bounds_12_3329 : exactInterval 12 3329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3329 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3329) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3329 : oddCount 3329 12 = 7 ∧ acceleratedOrbit 12 3329 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3329 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3329) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3329.1, data_12_3329.2]

/-- Complete interval computation for depth 12, residue 3330. -/
theorem bounds_12_3330 : exactInterval 12 3330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3330 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3330) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3330 : oddCount 3330 12 = 8 ∧ acceleratedOrbit 12 3330 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3330 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3330) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3330.1, data_12_3330.2]

/-- Complete interval computation for depth 12, residue 3331. -/
theorem bounds_12_3331 : exactInterval 12 3331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3331 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3331) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3331 : oddCount 3331 12 = 8 ∧ acceleratedOrbit 12 3331 = 5345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3331 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3331) = 3 ^ 8 * m + 5345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3331.1, data_12_3331.2]

/-- Complete interval computation for depth 12, residue 3332. -/
theorem bounds_12_3332 : exactInterval 12 3332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3332 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3332) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3332 : oddCount 3332 12 = 3 ∧ acceleratedOrbit 12 3332 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3332 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3332) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3332.1, data_12_3332.2]

end Collatz.Research.StoppingAtlas.Batch0417
