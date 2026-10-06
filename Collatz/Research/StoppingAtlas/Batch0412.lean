import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0412

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3240. -/
theorem bounds_12_3240 : exactInterval 12 3240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3240 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3240) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3240 : oddCount 3240 12 = 3 ∧ acceleratedOrbit 12 3240 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3240 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3240) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3240.1, data_12_3240.2]

/-- Complete interval computation for depth 12, residue 3241. -/
theorem bounds_12_3241 : exactInterval 12 3241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3241 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3241) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3241 : oddCount 3241 12 = 8 ∧ acceleratedOrbit 12 3241 = 5194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3241 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3241) = 3 ^ 8 * m + 5194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3241.1, data_12_3241.2]

/-- Complete interval computation for depth 12, residue 3242. -/
theorem bounds_12_3242 : exactInterval 12 3242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3242 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3242) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3242 : oddCount 3242 12 = 3 ∧ acceleratedOrbit 12 3242 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3242 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3242) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3242.1, data_12_3242.2]

/-- Complete interval computation for depth 12, residue 3243. -/
theorem bounds_12_3243 : exactInterval 12 3243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3243 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3243) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3243 : oddCount 3243 12 = 6 ∧ acceleratedOrbit 12 3243 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3243 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3243) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3243.1, data_12_3243.2]

/-- Complete interval computation for depth 12, residue 3244. -/
theorem bounds_12_3244 : exactInterval 12 3244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3244 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3244) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3244 : oddCount 3244 12 = 5 ∧ acceleratedOrbit 12 3244 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3244 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3244) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3244.1, data_12_3244.2]

/-- Complete interval computation for depth 12, residue 3245. -/
theorem bounds_12_3245 : exactInterval 12 3245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3245 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3245) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3245 : oddCount 3245 12 = 5 ∧ acceleratedOrbit 12 3245 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3245 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3245) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3245.1, data_12_3245.2]

/-- Complete interval computation for depth 12, residue 3246. -/
theorem bounds_12_3246 : exactInterval 12 3246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3246 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3246) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3246 : oddCount 3246 12 = 5 ∧ acceleratedOrbit 12 3246 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3246 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3246) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3246.1, data_12_3246.2]

/-- Complete interval computation for depth 12, residue 3247. -/
theorem bounds_12_3247 : exactInterval 12 3247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3247 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3247) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3247 : oddCount 3247 12 = 8 ∧ acceleratedOrbit 12 3247 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3247 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3247) = 3 ^ 8 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3247.1, data_12_3247.2]

/-- Complete interval computation for depth 12, residue 3248. -/
theorem bounds_12_3248 : exactInterval 12 3248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3248 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3248) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3248 : oddCount 3248 12 = 4 ∧ acceleratedOrbit 12 3248 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3248 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3248) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3248.1, data_12_3248.2]

/-- Complete interval computation for depth 12, residue 3249. -/
theorem bounds_12_3249 : exactInterval 12 3249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3249 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3249) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3249 : oddCount 3249 12 = 6 ∧ acceleratedOrbit 12 3249 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3249 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3249) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3249.1, data_12_3249.2]

/-- Complete interval computation for depth 12, residue 3250. -/
theorem bounds_12_3250 : exactInterval 12 3250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3250 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3250) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3250 : oddCount 3250 12 = 6 ∧ acceleratedOrbit 12 3250 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3250 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3250) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3250.1, data_12_3250.2]

/-- Complete interval computation for depth 12, residue 3251. -/
theorem bounds_12_3251 : exactInterval 12 3251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3251 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3251) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3251 : oddCount 3251 12 = 6 ∧ acceleratedOrbit 12 3251 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3251 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3251) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3251.1, data_12_3251.2]

/-- Complete interval computation for depth 12, residue 3252. -/
theorem bounds_12_3252 : exactInterval 12 3252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3252 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3252) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3252 : oddCount 3252 12 = 4 ∧ acceleratedOrbit 12 3252 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3252 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3252) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3252.1, data_12_3252.2]

/-- Complete interval computation for depth 12, residue 3253. -/
theorem bounds_12_3253 : exactInterval 12 3253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3253 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3253) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3253 : oddCount 3253 12 = 4 ∧ acceleratedOrbit 12 3253 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3253 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3253) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3253.1, data_12_3253.2]

/-- Complete interval computation for depth 12, residue 3254. -/
theorem bounds_12_3254 : exactInterval 12 3254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3254 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3254) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3254 : oddCount 3254 12 = 7 ∧ acceleratedOrbit 12 3254 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3254 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3254) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3254.1, data_12_3254.2]

/-- Complete interval computation for depth 12, residue 3255. -/
theorem bounds_12_3255 : exactInterval 12 3255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3255 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3255) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3255 : oddCount 3255 12 = 7 ∧ acceleratedOrbit 12 3255 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3255 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3255) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3255.1, data_12_3255.2]

end Collatz.Research.StoppingAtlas.Batch0412
