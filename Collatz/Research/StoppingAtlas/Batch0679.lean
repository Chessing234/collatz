import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0679

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3246. -/
theorem bounds_13_3246 : exactInterval 13 3246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3246 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3246) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3246 : oddCount 3246 13 = 6 ∧ acceleratedOrbit 13 3246 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3246 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3246) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3246.1, data_13_3246.2]

/-- Complete interval computation for depth 13, residue 3247. -/
theorem bounds_13_3247 : exactInterval 13 3247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3247 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3247) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3247 : oddCount 3247 13 = 8 ∧ acceleratedOrbit 13 3247 = 2602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3247 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3247) = 3 ^ 8 * m + 2602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3247.1, data_13_3247.2]

/-- Complete interval computation for depth 13, residue 3248. -/
theorem bounds_13_3248 : exactInterval 13 3248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3248 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3248) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3248 : oddCount 3248 13 = 5 ∧ acceleratedOrbit 13 3248 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3248 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3248) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3248.1, data_13_3248.2]

/-- Complete interval computation for depth 13, residue 3249. -/
theorem bounds_13_3249 : exactInterval 13 3249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3249 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3249) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3249 : oddCount 3249 13 = 6 ∧ acceleratedOrbit 13 3249 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3249 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3249) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3249.1, data_13_3249.2]

/-- Complete interval computation for depth 13, residue 3250. -/
theorem bounds_13_3250 : exactInterval 13 3250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3250 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3250) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3250 : oddCount 3250 13 = 6 ∧ acceleratedOrbit 13 3250 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3250 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3250) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3250.1, data_13_3250.2]

/-- Complete interval computation for depth 13, residue 3251. -/
theorem bounds_13_3251 : exactInterval 13 3251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3251 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3251) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3251 : oddCount 3251 13 = 6 ∧ acceleratedOrbit 13 3251 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3251 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3251) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3251.1, data_13_3251.2]

/-- Complete interval computation for depth 13, residue 3252. -/
theorem bounds_13_3252 : exactInterval 13 3252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3252 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3252) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3252 : oddCount 3252 13 = 5 ∧ acceleratedOrbit 13 3252 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3252 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3252) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3252.1, data_13_3252.2]

/-- Complete interval computation for depth 13, residue 3253. -/
theorem bounds_13_3253 : exactInterval 13 3253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3253 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3253) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3253 : oddCount 3253 13 = 5 ∧ acceleratedOrbit 13 3253 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3253 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3253) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3253.1, data_13_3253.2]

/-- Complete interval computation for depth 13, residue 3254. -/
theorem bounds_13_3254 : exactInterval 13 3254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3254 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3254) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3254 : oddCount 3254 13 = 8 ∧ acceleratedOrbit 13 3254 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3254 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3254) = 3 ^ 8 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3254.1, data_13_3254.2]

/-- Complete interval computation for depth 13, residue 3255. -/
theorem bounds_13_3255 : exactInterval 13 3255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3255 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3255) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3255 : oddCount 3255 13 = 8 ∧ acceleratedOrbit 13 3255 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3255 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3255) = 3 ^ 8 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3255.1, data_13_3255.2]

/-- Complete interval computation for depth 13, residue 3256. -/
theorem bounds_13_3256 : exactInterval 13 3256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3256 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3256) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3256 : oddCount 3256 13 = 5 ∧ acceleratedOrbit 13 3256 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3256 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3256) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3256.1, data_13_3256.2]

/-- Complete interval computation for depth 13, residue 3257. -/
theorem bounds_13_3257 : exactInterval 13 3257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3257 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3257) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3257 : oddCount 3257 13 = 8 ∧ acceleratedOrbit 13 3257 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3257 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3257) = 3 ^ 8 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3257.1, data_13_3257.2]

/-- Complete interval computation for depth 13, residue 3258. -/
theorem bounds_13_3258 : exactInterval 13 3258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3258 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3258) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3258 : oddCount 3258 13 = 5 ∧ acceleratedOrbit 13 3258 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3258 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3258) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3258.1, data_13_3258.2]

/-- Complete interval computation for depth 13, residue 3259. -/
theorem bounds_13_3259 : exactInterval 13 3259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3259 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3259) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3259 : oddCount 3259 13 = 8 ∧ acceleratedOrbit 13 3259 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3259 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3259) = 3 ^ 8 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3259.1, data_13_3259.2]

/-- Complete interval computation for depth 13, residue 3260. -/
theorem bounds_13_3260 : exactInterval 13 3260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3260 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3260) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3260 : oddCount 3260 13 = 7 ∧ acceleratedOrbit 13 3260 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3260 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3260) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3260.1, data_13_3260.2]

end Collatz.Research.StoppingAtlas.Batch0679
