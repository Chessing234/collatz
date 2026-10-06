import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0680

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3261. -/
theorem bounds_13_3261 : exactInterval 13 3261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3261 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3261) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3261 : oddCount 3261 13 = 7 ∧ acceleratedOrbit 13 3261 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3261 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3261) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3261.1, data_13_3261.2]

/-- Complete interval computation for depth 13, residue 3262. -/
theorem bounds_13_3262 : exactInterval 13 3262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3262 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3262) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3262 : oddCount 3262 13 = 7 ∧ acceleratedOrbit 13 3262 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3262 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3262) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3262.1, data_13_3262.2]

/-- Complete interval computation for depth 13, residue 3263. -/
theorem bounds_13_3263 : exactInterval 13 3263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3263 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3263) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3263 : oddCount 3263 13 = 9 ∧ acceleratedOrbit 13 3263 = 7843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3263 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3263) = 3 ^ 9 * m + 7843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3263.1, data_13_3263.2]

/-- Complete interval computation for depth 13, residue 3264. -/
theorem bounds_13_3264 : exactInterval 13 3264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3264 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3264) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3264 : oddCount 3264 13 = 3 ∧ acceleratedOrbit 13 3264 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3264 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3264) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3264.1, data_13_3264.2]

/-- Complete interval computation for depth 13, residue 3265. -/
theorem bounds_13_3265 : exactInterval 13 3265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3265 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3265) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3265 : oddCount 3265 13 = 5 ∧ acceleratedOrbit 13 3265 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3265 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3265) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3265.1, data_13_3265.2]

/-- Complete interval computation for depth 13, residue 3266. -/
theorem bounds_13_3266 : exactInterval 13 3266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3266 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3266) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3266 : oddCount 3266 13 = 5 ∧ acceleratedOrbit 13 3266 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3266 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3266) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3266.1, data_13_3266.2]

/-- Complete interval computation for depth 13, residue 3267. -/
theorem bounds_13_3267 : exactInterval 13 3267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3267 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3267) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3267 : oddCount 3267 13 = 5 ∧ acceleratedOrbit 13 3267 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3267 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3267) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3267.1, data_13_3267.2]

/-- Complete interval computation for depth 13, residue 3268. -/
theorem bounds_13_3268 : exactInterval 13 3268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3268 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3268) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3268 : oddCount 3268 13 = 5 ∧ acceleratedOrbit 13 3268 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3268 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3268) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3268.1, data_13_3268.2]

/-- Complete interval computation for depth 13, residue 3269. -/
theorem bounds_13_3269 : exactInterval 13 3269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3269 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3269) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3269 : oddCount 3269 13 = 5 ∧ acceleratedOrbit 13 3269 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3269 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3269) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3269.1, data_13_3269.2]

/-- Complete interval computation for depth 13, residue 3270. -/
theorem bounds_13_3270 : exactInterval 13 3270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3270 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3270) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3270 : oddCount 3270 13 = 5 ∧ acceleratedOrbit 13 3270 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3270 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3270) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3270.1, data_13_3270.2]

/-- Complete interval computation for depth 13, residue 3271. -/
theorem bounds_13_3271 : exactInterval 13 3271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3271 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3271) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3271 : oddCount 3271 13 = 7 ∧ acceleratedOrbit 13 3271 = 874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3271 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3271) = 3 ^ 7 * m + 874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3271.1, data_13_3271.2]

/-- Complete interval computation for depth 13, residue 3272. -/
theorem bounds_13_3272 : exactInterval 13 3272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3272 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3272) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3272 : oddCount 3272 13 = 5 ∧ acceleratedOrbit 13 3272 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3272 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3272) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3272.1, data_13_3272.2]

/-- Complete interval computation for depth 13, residue 3273. -/
theorem bounds_13_3273 : exactInterval 13 3273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3273 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3273) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3273 : oddCount 3273 13 = 6 ∧ acceleratedOrbit 13 3273 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3273 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3273) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3273.1, data_13_3273.2]

/-- Complete interval computation for depth 13, residue 3274. -/
theorem bounds_13_3274 : exactInterval 13 3274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3274 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3274) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3274 : oddCount 3274 13 = 5 ∧ acceleratedOrbit 13 3274 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3274 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3274) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3274.1, data_13_3274.2]

/-- Complete interval computation for depth 13, residue 3275. -/
theorem bounds_13_3275 : exactInterval 13 3275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3275 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3275) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3275 : oddCount 3275 13 = 6 ∧ acceleratedOrbit 13 3275 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3275 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3275) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3275.1, data_13_3275.2]

end Collatz.Research.StoppingAtlas.Batch0680
