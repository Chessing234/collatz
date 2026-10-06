import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0100

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3244. -/
theorem bounds_15_3244 : exactInterval 15 3244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3244 : oddCount 3244 15 = 7 ∧ acceleratedOrbit 15 3244 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3244) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3244.1, data_15_3244.2]

/-- Complete interval computation for depth 15, residue 3245. -/
theorem bounds_15_3245 : exactInterval 15 3245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3245 : oddCount 3245 15 = 7 ∧ acceleratedOrbit 15 3245 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3245) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3245.1, data_15_3245.2]

/-- Complete interval computation for depth 15, residue 3246. -/
theorem bounds_15_3246 : exactInterval 15 3246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3246 : oddCount 3246 15 = 7 ∧ acceleratedOrbit 15 3246 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3246) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3246.1, data_15_3246.2]

/-- Complete interval computation for depth 15, residue 3247. -/
theorem bounds_15_3247 : exactInterval 15 3247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3247 : oddCount 3247 15 = 9 ∧ acceleratedOrbit 15 3247 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3247) = 3 ^ 9 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3247.1, data_15_3247.2]

/-- Complete interval computation for depth 15, residue 3248. -/
theorem bounds_15_3248 : exactInterval 15 3248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3248 : oddCount 3248 15 = 6 ∧ acceleratedOrbit 15 3248 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3248) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3248.1, data_15_3248.2]

/-- Complete interval computation for depth 15, residue 3249. -/
theorem bounds_15_3249 : exactInterval 15 3249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3249 : oddCount 3249 15 = 7 ∧ acceleratedOrbit 15 3249 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3249) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3249.1, data_15_3249.2]

/-- Complete interval computation for depth 15, residue 3250. -/
theorem bounds_15_3250 : exactInterval 15 3250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3250 : oddCount 3250 15 = 7 ∧ acceleratedOrbit 15 3250 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3250) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3250.1, data_15_3250.2]

/-- Complete interval computation for depth 15, residue 3251. -/
theorem bounds_15_3251 : exactInterval 15 3251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3251 : oddCount 3251 15 = 7 ∧ acceleratedOrbit 15 3251 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3251) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3251.1, data_15_3251.2]

/-- Complete interval computation for depth 15, residue 3252. -/
theorem bounds_15_3252 : exactInterval 15 3252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3252 : oddCount 3252 15 = 6 ∧ acceleratedOrbit 15 3252 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3252) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3252.1, data_15_3252.2]

/-- Complete interval computation for depth 15, residue 3253. -/
theorem bounds_15_3253 : exactInterval 15 3253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3253 : oddCount 3253 15 = 6 ∧ acceleratedOrbit 15 3253 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3253) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3253.1, data_15_3253.2]

/-- Complete interval computation for depth 15, residue 3254. -/
theorem bounds_15_3254 : exactInterval 15 3254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3254 : oddCount 3254 15 = 9 ∧ acceleratedOrbit 15 3254 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3254) = 3 ^ 9 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3254.1, data_15_3254.2]

/-- Complete interval computation for depth 15, residue 3255. -/
theorem bounds_15_3255 : exactInterval 15 3255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3255 : oddCount 3255 15 = 9 ∧ acceleratedOrbit 15 3255 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3255) = 3 ^ 9 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3255.1, data_15_3255.2]

/-- Complete interval computation for depth 15, residue 3256. -/
theorem bounds_15_3256 : exactInterval 15 3256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3256 : oddCount 3256 15 = 6 ∧ acceleratedOrbit 15 3256 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3256) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3256.1, data_15_3256.2]

/-- Complete interval computation for depth 15, residue 3257. -/
theorem bounds_15_3257 : exactInterval 15 3257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3257 : oddCount 3257 15 = 8 ∧ acceleratedOrbit 15 3257 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3257) = 3 ^ 8 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3257.1, data_15_3257.2]

/-- Complete interval computation for depth 15, residue 3258. -/
theorem bounds_15_3258 : exactInterval 15 3258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3258 : oddCount 3258 15 = 6 ∧ acceleratedOrbit 15 3258 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3258) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3258.1, data_15_3258.2]

/-- Complete interval computation for depth 15, residue 3259. -/
theorem bounds_15_3259 : exactInterval 15 3259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3259 : oddCount 3259 15 = 8 ∧ acceleratedOrbit 15 3259 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3259) = 3 ^ 8 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3259.1, data_15_3259.2]

/-- Complete interval computation for depth 15, residue 3260. -/
theorem bounds_15_3260 : exactInterval 15 3260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3260 : oddCount 3260 15 = 7 ∧ acceleratedOrbit 15 3260 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3260) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3260.1, data_15_3260.2]

/-- Complete interval computation for depth 15, residue 3261. -/
theorem bounds_15_3261 : exactInterval 15 3261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3261 : oddCount 3261 15 = 7 ∧ acceleratedOrbit 15 3261 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3261) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3261.1, data_15_3261.2]

/-- Complete interval computation for depth 15, residue 3262. -/
theorem bounds_15_3262 : exactInterval 15 3262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3262 : oddCount 3262 15 = 7 ∧ acceleratedOrbit 15 3262 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3262) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3262.1, data_15_3262.2]

/-- Complete interval computation for depth 15, residue 3263. -/
theorem bounds_15_3263 : exactInterval 15 3263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3263 : oddCount 3263 15 = 11 ∧ acceleratedOrbit 15 3263 = 17648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3263) = 3 ^ 11 * m + 17648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3263.1, data_15_3263.2]

/-- Complete interval computation for depth 15, residue 3264. -/
theorem bounds_15_3264 : exactInterval 15 3264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3264 : oddCount 3264 15 = 5 ∧ acceleratedOrbit 15 3264 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3264) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3264.1, data_15_3264.2]

/-- Complete interval computation for depth 15, residue 3265. -/
theorem bounds_15_3265 : exactInterval 15 3265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3265 : oddCount 3265 15 = 6 ∧ acceleratedOrbit 15 3265 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3265) = 3 ^ 6 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3265.1, data_15_3265.2]

/-- Complete interval computation for depth 15, residue 3266. -/
theorem bounds_15_3266 : exactInterval 15 3266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3266 : oddCount 3266 15 = 6 ∧ acceleratedOrbit 15 3266 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3266) = 3 ^ 6 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3266.1, data_15_3266.2]

/-- Complete interval computation for depth 15, residue 3267. -/
theorem bounds_15_3267 : exactInterval 15 3267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3267 : oddCount 3267 15 = 6 ∧ acceleratedOrbit 15 3267 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3267) = 3 ^ 6 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3267.1, data_15_3267.2]

/-- Complete interval computation for depth 15, residue 3268. -/
theorem bounds_15_3268 : exactInterval 15 3268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3268 : oddCount 3268 15 = 6 ∧ acceleratedOrbit 15 3268 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3268) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3268.1, data_15_3268.2]

/-- Complete interval computation for depth 15, residue 3269. -/
theorem bounds_15_3269 : exactInterval 15 3269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3269 : oddCount 3269 15 = 6 ∧ acceleratedOrbit 15 3269 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3269) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3269.1, data_15_3269.2]

/-- Complete interval computation for depth 15, residue 3270. -/
theorem bounds_15_3270 : exactInterval 15 3270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3270 : oddCount 3270 15 = 6 ∧ acceleratedOrbit 15 3270 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3270) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3270.1, data_15_3270.2]

/-- Complete interval computation for depth 15, residue 3271. -/
theorem bounds_15_3271 : exactInterval 15 3271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3271 : oddCount 3271 15 = 8 ∧ acceleratedOrbit 15 3271 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3271) = 3 ^ 8 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3271.1, data_15_3271.2]

/-- Complete interval computation for depth 15, residue 3272. -/
theorem bounds_15_3272 : exactInterval 15 3272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3272 : oddCount 3272 15 = 6 ∧ acceleratedOrbit 15 3272 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3272) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3272.1, data_15_3272.2]

/-- Complete interval computation for depth 15, residue 3273. -/
theorem bounds_15_3273 : exactInterval 15 3273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3273 : oddCount 3273 15 = 6 ∧ acceleratedOrbit 15 3273 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3273) = 3 ^ 6 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3273.1, data_15_3273.2]

/-- Complete interval computation for depth 15, residue 3274. -/
theorem bounds_15_3274 : exactInterval 15 3274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3274 : oddCount 3274 15 = 6 ∧ acceleratedOrbit 15 3274 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3274) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3274.1, data_15_3274.2]

/-- Complete interval computation for depth 15, residue 3275. -/
theorem bounds_15_3275 : exactInterval 15 3275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3275 : oddCount 3275 15 = 6 ∧ acceleratedOrbit 15 3275 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3275) = 3 ^ 6 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3275.1, data_15_3275.2]

end Collatz.Research.PassageAtlas.Batch0100
