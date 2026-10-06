import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0102

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3309. -/
theorem bounds_15_3309 : exactInterval 15 3309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3309 : oddCount 3309 15 = 6 ∧ acceleratedOrbit 15 3309 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3309) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3309.1, data_15_3309.2]

/-- Complete interval computation for depth 15, residue 3310. -/
theorem bounds_15_3310 : exactInterval 15 3310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3310 : oddCount 3310 15 = 6 ∧ acceleratedOrbit 15 3310 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3310) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3310.1, data_15_3310.2]

/-- Complete interval computation for depth 15, residue 3311. -/
theorem bounds_15_3311 : exactInterval 15 3311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3311 : oddCount 3311 15 = 11 ∧ acceleratedOrbit 15 3311 = 17906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3311) = 3 ^ 11 * m + 17906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3311.1, data_15_3311.2]

/-- Complete interval computation for depth 15, residue 3312. -/
theorem bounds_15_3312 : exactInterval 15 3312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3312 : oddCount 3312 15 = 8 ∧ acceleratedOrbit 15 3312 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3312) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3312.1, data_15_3312.2]

/-- Complete interval computation for depth 15, residue 3313. -/
theorem bounds_15_3313 : exactInterval 15 3313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3313 : oddCount 3313 15 = 8 ∧ acceleratedOrbit 15 3313 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3313) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3313.1, data_15_3313.2]

/-- Complete interval computation for depth 15, residue 3314. -/
theorem bounds_15_3314 : exactInterval 15 3314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3314 : oddCount 3314 15 = 8 ∧ acceleratedOrbit 15 3314 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3314) = 3 ^ 8 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3314.1, data_15_3314.2]

/-- Complete interval computation for depth 15, residue 3315. -/
theorem bounds_15_3315 : exactInterval 15 3315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3315 : oddCount 3315 15 = 8 ∧ acceleratedOrbit 15 3315 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3315) = 3 ^ 8 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3315.1, data_15_3315.2]

/-- Complete interval computation for depth 15, residue 3316. -/
theorem bounds_15_3316 : exactInterval 15 3316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3316 : oddCount 3316 15 = 8 ∧ acceleratedOrbit 15 3316 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3316) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3316.1, data_15_3316.2]

/-- Complete interval computation for depth 15, residue 3317. -/
theorem bounds_15_3317 : exactInterval 15 3317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3317 : oddCount 3317 15 = 8 ∧ acceleratedOrbit 15 3317 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3317) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3317.1, data_15_3317.2]

/-- Complete interval computation for depth 15, residue 3318. -/
theorem bounds_15_3318 : exactInterval 15 3318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3318 : oddCount 3318 15 = 6 ∧ acceleratedOrbit 15 3318 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3318) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3318.1, data_15_3318.2]

/-- Complete interval computation for depth 15, residue 3319. -/
theorem bounds_15_3319 : exactInterval 15 3319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3319 : oddCount 3319 15 = 6 ∧ acceleratedOrbit 15 3319 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3319) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3319.1, data_15_3319.2]

/-- Complete interval computation for depth 15, residue 3320. -/
theorem bounds_15_3320 : exactInterval 15 3320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3320 : oddCount 3320 15 = 9 ∧ acceleratedOrbit 15 3320 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3320) = 3 ^ 9 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3320.1, data_15_3320.2]

/-- Complete interval computation for depth 15, residue 3321. -/
theorem bounds_15_3321 : exactInterval 15 3321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3321 : oddCount 3321 15 = 10 ∧ acceleratedOrbit 15 3321 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3321) = 3 ^ 10 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3321.1, data_15_3321.2]

/-- Complete interval computation for depth 15, residue 3322. -/
theorem bounds_15_3322 : exactInterval 15 3322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3322 : oddCount 3322 15 = 9 ∧ acceleratedOrbit 15 3322 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3322) = 3 ^ 9 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3322.1, data_15_3322.2]

/-- Complete interval computation for depth 15, residue 3323. -/
theorem bounds_15_3323 : exactInterval 15 3323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3323 : oddCount 3323 15 = 11 ∧ acceleratedOrbit 15 3323 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3323) = 3 ^ 11 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3323.1, data_15_3323.2]

/-- Complete interval computation for depth 15, residue 3324. -/
theorem bounds_15_3324 : exactInterval 15 3324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3324 : oddCount 3324 15 = 9 ∧ acceleratedOrbit 15 3324 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3324) = 3 ^ 9 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3324.1, data_15_3324.2]

/-- Complete interval computation for depth 15, residue 3325. -/
theorem bounds_15_3325 : exactInterval 15 3325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3325 : oddCount 3325 15 = 9 ∧ acceleratedOrbit 15 3325 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3325) = 3 ^ 9 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3325.1, data_15_3325.2]

/-- Complete interval computation for depth 15, residue 3326. -/
theorem bounds_15_3326 : exactInterval 15 3326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3326 : oddCount 3326 15 = 11 ∧ acceleratedOrbit 15 3326 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3326) = 3 ^ 11 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3326.1, data_15_3326.2]

/-- Complete interval computation for depth 15, residue 3327. -/
theorem bounds_15_3327 : exactInterval 15 3327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3327 : oddCount 3327 15 = 11 ∧ acceleratedOrbit 15 3327 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3327) = 3 ^ 11 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3327.1, data_15_3327.2]

/-- Complete interval computation for depth 15, residue 3328. -/
theorem bounds_15_3328 : exactInterval 15 3328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3328 : oddCount 3328 15 = 2 ∧ acceleratedOrbit 15 3328 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3328) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3328.1, data_15_3328.2]

/-- Complete interval computation for depth 15, residue 3329. -/
theorem bounds_15_3329 : exactInterval 15 3329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3329 : oddCount 3329 15 = 8 ∧ acceleratedOrbit 15 3329 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3329) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3329.1, data_15_3329.2]

/-- Complete interval computation for depth 15, residue 3330. -/
theorem bounds_15_3330 : exactInterval 15 3330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3330 : oddCount 3330 15 = 10 ∧ acceleratedOrbit 15 3330 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3330) = 3 ^ 10 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3330.1, data_15_3330.2]

/-- Complete interval computation for depth 15, residue 3331. -/
theorem bounds_15_3331 : exactInterval 15 3331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3331 : oddCount 3331 15 = 10 ∧ acceleratedOrbit 15 3331 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3331) = 3 ^ 10 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3331.1, data_15_3331.2]

/-- Complete interval computation for depth 15, residue 3332. -/
theorem bounds_15_3332 : exactInterval 15 3332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3332 : oddCount 3332 15 = 5 ∧ acceleratedOrbit 15 3332 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3332) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3332.1, data_15_3332.2]

/-- Complete interval computation for depth 15, residue 3333. -/
theorem bounds_15_3333 : exactInterval 15 3333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3333 : oddCount 3333 15 = 5 ∧ acceleratedOrbit 15 3333 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3333) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3333.1, data_15_3333.2]

/-- Complete interval computation for depth 15, residue 3334. -/
theorem bounds_15_3334 : exactInterval 15 3334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3334 : oddCount 3334 15 = 5 ∧ acceleratedOrbit 15 3334 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3334) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3334.1, data_15_3334.2]

/-- Complete interval computation for depth 15, residue 3335. -/
theorem bounds_15_3335 : exactInterval 15 3335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3335 : oddCount 3335 15 = 10 ∧ acceleratedOrbit 15 3335 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3335) = 3 ^ 10 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3335.1, data_15_3335.2]

/-- Complete interval computation for depth 15, residue 3336. -/
theorem bounds_15_3336 : exactInterval 15 3336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3336 : oddCount 3336 15 = 8 ∧ acceleratedOrbit 15 3336 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3336) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3336.1, data_15_3336.2]

/-- Complete interval computation for depth 15, residue 3337. -/
theorem bounds_15_3337 : exactInterval 15 3337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3337 : oddCount 3337 15 = 10 ∧ acceleratedOrbit 15 3337 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3337) = 3 ^ 10 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3337.1, data_15_3337.2]

/-- Complete interval computation for depth 15, residue 3338. -/
theorem bounds_15_3338 : exactInterval 15 3338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3338 : oddCount 3338 15 = 8 ∧ acceleratedOrbit 15 3338 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3338) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3338.1, data_15_3338.2]

/-- Complete interval computation for depth 15, residue 3339. -/
theorem bounds_15_3339 : exactInterval 15 3339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3339 : oddCount 3339 15 = 8 ∧ acceleratedOrbit 15 3339 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3339) = 3 ^ 8 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3339.1, data_15_3339.2]

/-- Complete interval computation for depth 15, residue 3340. -/
theorem bounds_15_3340 : exactInterval 15 3340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3340 : oddCount 3340 15 = 8 ∧ acceleratedOrbit 15 3340 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3340) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3340.1, data_15_3340.2]

/-- Complete interval computation for depth 15, residue 3341. -/
theorem bounds_15_3341 : exactInterval 15 3341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3341 : oddCount 3341 15 = 8 ∧ acceleratedOrbit 15 3341 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3341) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3341.1, data_15_3341.2]

end Collatz.Research.PassageAtlas.Batch0102
