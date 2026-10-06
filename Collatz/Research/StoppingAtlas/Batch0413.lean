import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0413

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3256. -/
theorem bounds_12_3256 : exactInterval 12 3256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3256 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3256) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3256 : oddCount 3256 12 = 4 ∧ acceleratedOrbit 12 3256 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3256 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3256) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3256.1, data_12_3256.2]

/-- Complete interval computation for depth 12, residue 3257. -/
theorem bounds_12_3257 : exactInterval 12 3257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3257 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3257) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3257 : oddCount 3257 12 = 7 ∧ acceleratedOrbit 12 3257 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3257 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3257) = 3 ^ 7 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3257.1, data_12_3257.2]

/-- Complete interval computation for depth 12, residue 3258. -/
theorem bounds_12_3258 : exactInterval 12 3258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3258 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3258) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3258 : oddCount 3258 12 = 4 ∧ acceleratedOrbit 12 3258 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3258 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3258) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3258.1, data_12_3258.2]

/-- Complete interval computation for depth 12, residue 3259. -/
theorem bounds_12_3259 : exactInterval 12 3259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3259 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3259) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3259 : oddCount 3259 12 = 8 ∧ acceleratedOrbit 12 3259 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3259 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3259) = 3 ^ 8 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3259.1, data_12_3259.2]

/-- Complete interval computation for depth 12, residue 3260. -/
theorem bounds_12_3260 : exactInterval 12 3260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3260 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3260) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3260 : oddCount 3260 12 = 6 ∧ acceleratedOrbit 12 3260 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3260 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3260) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3260.1, data_12_3260.2]

/-- Complete interval computation for depth 12, residue 3261. -/
theorem bounds_12_3261 : exactInterval 12 3261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3261 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3261) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3261 : oddCount 3261 12 = 6 ∧ acceleratedOrbit 12 3261 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3261 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3261) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3261.1, data_12_3261.2]

/-- Complete interval computation for depth 12, residue 3262. -/
theorem bounds_12_3262 : exactInterval 12 3262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3262 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3262) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3262 : oddCount 3262 12 = 6 ∧ acceleratedOrbit 12 3262 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3262 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3262) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3262.1, data_12_3262.2]

/-- Complete interval computation for depth 12, residue 3263. -/
theorem bounds_12_3263 : exactInterval 12 3263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3263 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3263) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3263 : oddCount 3263 12 = 9 ∧ acceleratedOrbit 12 3263 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3263 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3263) = 3 ^ 9 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3263.1, data_12_3263.2]

/-- Complete interval computation for depth 12, residue 3264. -/
theorem bounds_12_3264 : exactInterval 12 3264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3264 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3264) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3264 : oddCount 3264 12 = 3 ∧ acceleratedOrbit 12 3264 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3264 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3264) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3264.1, data_12_3264.2]

/-- Complete interval computation for depth 12, residue 3265. -/
theorem bounds_12_3265 : exactInterval 12 3265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3265 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3265) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3265 : oddCount 3265 12 = 5 ∧ acceleratedOrbit 12 3265 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3265 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3265) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3265.1, data_12_3265.2]

/-- Complete interval computation for depth 12, residue 3266. -/
theorem bounds_12_3266 : exactInterval 12 3266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3266 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3266) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3266 : oddCount 3266 12 = 5 ∧ acceleratedOrbit 12 3266 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3266 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3266) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3266.1, data_12_3266.2]

/-- Complete interval computation for depth 12, residue 3267. -/
theorem bounds_12_3267 : exactInterval 12 3267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3267 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3267) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3267 : oddCount 3267 12 = 5 ∧ acceleratedOrbit 12 3267 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3267 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3267) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3267.1, data_12_3267.2]

/-- Complete interval computation for depth 12, residue 3268. -/
theorem bounds_12_3268 : exactInterval 12 3268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3268 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3268) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3268 : oddCount 3268 12 = 4 ∧ acceleratedOrbit 12 3268 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3268 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3268) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3268.1, data_12_3268.2]

/-- Complete interval computation for depth 12, residue 3269. -/
theorem bounds_12_3269 : exactInterval 12 3269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3269 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3269) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3269 : oddCount 3269 12 = 4 ∧ acceleratedOrbit 12 3269 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3269 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3269) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3269.1, data_12_3269.2]

/-- Complete interval computation for depth 12, residue 3270. -/
theorem bounds_12_3270 : exactInterval 12 3270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3270 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3270) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3270 : oddCount 3270 12 = 4 ∧ acceleratedOrbit 12 3270 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3270 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3270) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3270.1, data_12_3270.2]

end Collatz.Research.StoppingAtlas.Batch0413
