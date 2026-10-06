import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0683

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3307. -/
theorem bounds_13_3307 : exactInterval 13 3307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3307 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3307) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3307 : oddCount 3307 13 = 9 ∧ acceleratedOrbit 13 3307 = 7951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3307 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3307) = 3 ^ 9 * m + 7951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3307.1, data_13_3307.2]

/-- Complete interval computation for depth 13, residue 3308. -/
theorem bounds_13_3308 : exactInterval 13 3308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3308 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3308) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3308 : oddCount 3308 13 = 6 ∧ acceleratedOrbit 13 3308 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3308 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3308) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3308.1, data_13_3308.2]

/-- Complete interval computation for depth 13, residue 3309. -/
theorem bounds_13_3309 : exactInterval 13 3309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3309 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3309) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3309 : oddCount 3309 13 = 6 ∧ acceleratedOrbit 13 3309 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3309 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3309) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3309.1, data_13_3309.2]

/-- Complete interval computation for depth 13, residue 3310. -/
theorem bounds_13_3310 : exactInterval 13 3310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3310 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3310) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3310 : oddCount 3310 13 = 6 ∧ acceleratedOrbit 13 3310 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3310 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3310) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3310.1, data_13_3310.2]

/-- Complete interval computation for depth 13, residue 3311. -/
theorem bounds_13_3311 : exactInterval 13 3311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3311 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3311) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3311 : oddCount 3311 13 = 11 ∧ acceleratedOrbit 13 3311 = 71624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3311 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3311) = 3 ^ 11 * m + 71624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3311.1, data_13_3311.2]

/-- Complete interval computation for depth 13, residue 3312. -/
theorem bounds_13_3312 : exactInterval 13 3312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3312 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3312) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3312 : oddCount 3312 13 = 7 ∧ acceleratedOrbit 13 3312 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3312 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3312) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3312.1, data_13_3312.2]

/-- Complete interval computation for depth 13, residue 3313. -/
theorem bounds_13_3313 : exactInterval 13 3313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3313 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3313) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3313 : oddCount 3313 13 = 7 ∧ acceleratedOrbit 13 3313 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3313 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3313) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3313.1, data_13_3313.2]

/-- Complete interval computation for depth 13, residue 3314. -/
theorem bounds_13_3314 : exactInterval 13 3314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3314 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3314) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3314 : oddCount 3314 13 = 7 ∧ acceleratedOrbit 13 3314 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3314 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3314) = 3 ^ 7 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3314.1, data_13_3314.2]

/-- Complete interval computation for depth 13, residue 3315. -/
theorem bounds_13_3315 : exactInterval 13 3315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3315 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3315) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3315 : oddCount 3315 13 = 7 ∧ acceleratedOrbit 13 3315 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3315 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3315) = 3 ^ 7 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3315.1, data_13_3315.2]

/-- Complete interval computation for depth 13, residue 3316. -/
theorem bounds_13_3316 : exactInterval 13 3316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3316 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3316) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3316 : oddCount 3316 13 = 7 ∧ acceleratedOrbit 13 3316 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3316 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3316) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3316.1, data_13_3316.2]

/-- Complete interval computation for depth 13, residue 3317. -/
theorem bounds_13_3317 : exactInterval 13 3317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3317 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3317) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3317 : oddCount 3317 13 = 7 ∧ acceleratedOrbit 13 3317 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3317 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3317) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3317.1, data_13_3317.2]

/-- Complete interval computation for depth 13, residue 3318. -/
theorem bounds_13_3318 : exactInterval 13 3318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3318 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3318) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3318 : oddCount 3318 13 = 6 ∧ acceleratedOrbit 13 3318 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3318 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3318) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3318.1, data_13_3318.2]

/-- Complete interval computation for depth 13, residue 3319. -/
theorem bounds_13_3319 : exactInterval 13 3319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3319 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3319) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3319 : oddCount 3319 13 = 6 ∧ acceleratedOrbit 13 3319 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3319 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3319) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3319.1, data_13_3319.2]

/-- Complete interval computation for depth 13, residue 3320. -/
theorem bounds_13_3320 : exactInterval 13 3320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3320 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3320) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3320 : oddCount 3320 13 = 8 ∧ acceleratedOrbit 13 3320 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3320 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3320) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3320.1, data_13_3320.2]

/-- Complete interval computation for depth 13, residue 3321. -/
theorem bounds_13_3321 : exactInterval 13 3321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3321 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3321) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3321 : oddCount 3321 13 = 8 ∧ acceleratedOrbit 13 3321 = 2663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3321 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3321) = 3 ^ 8 * m + 2663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3321.1, data_13_3321.2]

end Collatz.Research.StoppingAtlas.Batch0683
