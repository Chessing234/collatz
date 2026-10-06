import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0416

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3302. -/
theorem bounds_12_3302 : exactInterval 12 3302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3302 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3302) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3302 : oddCount 3302 12 = 6 ∧ acceleratedOrbit 12 3302 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3302 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3302) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3302.1, data_12_3302.2]

/-- Complete interval computation for depth 12, residue 3303. -/
theorem bounds_12_3303 : exactInterval 12 3303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3303 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3303) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3303 : oddCount 3303 12 = 8 ∧ acceleratedOrbit 12 3303 = 5293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3303 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3303) = 3 ^ 8 * m + 5293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3303.1, data_12_3303.2]

/-- Complete interval computation for depth 12, residue 3304. -/
theorem bounds_12_3304 : exactInterval 12 3304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3304 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3304) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3304 : oddCount 3304 12 = 6 ∧ acceleratedOrbit 12 3304 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3304 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3304) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3304.1, data_12_3304.2]

/-- Complete interval computation for depth 12, residue 3305. -/
theorem bounds_12_3305 : exactInterval 12 3305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3305 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3305) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3305 : oddCount 3305 12 = 7 ∧ acceleratedOrbit 12 3305 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3305 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3305) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3305.1, data_12_3305.2]

/-- Complete interval computation for depth 12, residue 3306. -/
theorem bounds_12_3306 : exactInterval 12 3306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3306 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3306) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3306 : oddCount 3306 12 = 6 ∧ acceleratedOrbit 12 3306 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3306 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3306) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3306.1, data_12_3306.2]

/-- Complete interval computation for depth 12, residue 3307. -/
theorem bounds_12_3307 : exactInterval 12 3307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3307 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3307) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3307 : oddCount 3307 12 = 9 ∧ acceleratedOrbit 12 3307 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3307 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3307) = 3 ^ 9 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3307.1, data_12_3307.2]

/-- Complete interval computation for depth 12, residue 3308. -/
theorem bounds_12_3308 : exactInterval 12 3308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3308 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3308) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3308 : oddCount 3308 12 = 5 ∧ acceleratedOrbit 12 3308 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3308 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3308) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3308.1, data_12_3308.2]

/-- Complete interval computation for depth 12, residue 3309. -/
theorem bounds_12_3309 : exactInterval 12 3309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3309 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3309) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3309 : oddCount 3309 12 = 5 ∧ acceleratedOrbit 12 3309 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3309 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3309) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3309.1, data_12_3309.2]

/-- Complete interval computation for depth 12, residue 3310. -/
theorem bounds_12_3310 : exactInterval 12 3310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3310 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3310) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3310 : oddCount 3310 12 = 5 ∧ acceleratedOrbit 12 3310 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3310 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3310) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3310.1, data_12_3310.2]

/-- Complete interval computation for depth 12, residue 3311. -/
theorem bounds_12_3311 : exactInterval 12 3311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3311 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3311) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3311 : oddCount 3311 12 = 10 ∧ acceleratedOrbit 12 3311 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3311 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3311) = 3 ^ 10 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3311.1, data_12_3311.2]

/-- Complete interval computation for depth 12, residue 3312. -/
theorem bounds_12_3312 : exactInterval 12 3312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3312 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3312) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3312 : oddCount 3312 12 = 6 ∧ acceleratedOrbit 12 3312 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3312 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3312) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3312.1, data_12_3312.2]

/-- Complete interval computation for depth 12, residue 3313. -/
theorem bounds_12_3313 : exactInterval 12 3313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3313 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3313) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3313 : oddCount 3313 12 = 6 ∧ acceleratedOrbit 12 3313 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3313 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3313) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3313.1, data_12_3313.2]

/-- Complete interval computation for depth 12, residue 3314. -/
theorem bounds_12_3314 : exactInterval 12 3314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3314 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3314) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3314 : oddCount 3314 12 = 7 ∧ acceleratedOrbit 12 3314 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3314 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3314) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3314.1, data_12_3314.2]

/-- Complete interval computation for depth 12, residue 3315. -/
theorem bounds_12_3315 : exactInterval 12 3315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3315 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3315) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3315 : oddCount 3315 12 = 7 ∧ acceleratedOrbit 12 3315 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3315 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3315) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3315.1, data_12_3315.2]

/-- Complete interval computation for depth 12, residue 3316. -/
theorem bounds_12_3316 : exactInterval 12 3316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3316 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3316) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3316 : oddCount 3316 12 = 6 ∧ acceleratedOrbit 12 3316 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3316 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3316) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3316.1, data_12_3316.2]

end Collatz.Research.StoppingAtlas.Batch0416
