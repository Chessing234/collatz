import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0348

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2257. -/
theorem bounds_12_2257 : exactInterval 12 2257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2257 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2257) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2257 : oddCount 2257 12 = 7 ∧ acceleratedOrbit 12 2257 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2257 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2257) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2257.1, data_12_2257.2]

/-- Complete interval computation for depth 12, residue 2258. -/
theorem bounds_12_2258 : exactInterval 12 2258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2258 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2258) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2258 : oddCount 2258 12 = 7 ∧ acceleratedOrbit 12 2258 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2258 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2258) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2258.1, data_12_2258.2]

/-- Complete interval computation for depth 12, residue 2259. -/
theorem bounds_12_2259 : exactInterval 12 2259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2259 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2259) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2259 : oddCount 2259 12 = 7 ∧ acceleratedOrbit 12 2259 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2259 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2259) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2259.1, data_12_2259.2]

/-- Complete interval computation for depth 12, residue 2260. -/
theorem bounds_12_2260 : exactInterval 12 2260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2260 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2260) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2260 : oddCount 2260 12 = 2 ∧ acceleratedOrbit 12 2260 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2260 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2260) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2260.1, data_12_2260.2]

/-- Complete interval computation for depth 12, residue 2261. -/
theorem bounds_12_2261 : exactInterval 12 2261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2261 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2261) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2261 : oddCount 2261 12 = 2 ∧ acceleratedOrbit 12 2261 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2261 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2261) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2261.1, data_12_2261.2]

/-- Complete interval computation for depth 12, residue 2262. -/
theorem bounds_12_2262 : exactInterval 12 2262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2262 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2262) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2262 : oddCount 2262 12 = 7 ∧ acceleratedOrbit 12 2262 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2262 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2262) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2262.1, data_12_2262.2]

/-- Complete interval computation for depth 12, residue 2263. -/
theorem bounds_12_2263 : exactInterval 12 2263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2263 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2263) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2263 : oddCount 2263 12 = 7 ∧ acceleratedOrbit 12 2263 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2263 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2263) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2263.1, data_12_2263.2]

/-- Complete interval computation for depth 12, residue 2264. -/
theorem bounds_12_2264 : exactInterval 12 2264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2264 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2264) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2264 : oddCount 2264 12 = 8 ∧ acceleratedOrbit 12 2264 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2264 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2264) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2264.1, data_12_2264.2]

/-- Complete interval computation for depth 12, residue 2265. -/
theorem bounds_12_2265 : exactInterval 12 2265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2265 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2265) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2265 : oddCount 2265 12 = 7 ∧ acceleratedOrbit 12 2265 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2265 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2265) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2265.1, data_12_2265.2]

/-- Complete interval computation for depth 12, residue 2266. -/
theorem bounds_12_2266 : exactInterval 12 2266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2266 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2266) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2266 : oddCount 2266 12 = 8 ∧ acceleratedOrbit 12 2266 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2266 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2266) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2266.1, data_12_2266.2]

/-- Complete interval computation for depth 12, residue 2267. -/
theorem bounds_12_2267 : exactInterval 12 2267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2267 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2267) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2267 : oddCount 2267 12 = 8 ∧ acceleratedOrbit 12 2267 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2267 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2267) = 3 ^ 8 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2267.1, data_12_2267.2]

/-- Complete interval computation for depth 12, residue 2268. -/
theorem bounds_12_2268 : exactInterval 12 2268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2268 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2268) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2268 : oddCount 2268 12 = 8 ∧ acceleratedOrbit 12 2268 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2268 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2268) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2268.1, data_12_2268.2]

/-- Complete interval computation for depth 12, residue 2269. -/
theorem bounds_12_2269 : exactInterval 12 2269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2269 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2269) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2269 : oddCount 2269 12 = 8 ∧ acceleratedOrbit 12 2269 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2269 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2269) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2269.1, data_12_2269.2]

/-- Complete interval computation for depth 12, residue 2270. -/
theorem bounds_12_2270 : exactInterval 12 2270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2270 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2270) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2270 : oddCount 2270 12 = 8 ∧ acceleratedOrbit 12 2270 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2270 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2270) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2270.1, data_12_2270.2]

/-- Complete interval computation for depth 12, residue 2271. -/
theorem bounds_12_2271 : exactInterval 12 2271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2271 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2271) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2271 : oddCount 2271 12 = 8 ∧ acceleratedOrbit 12 2271 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2271 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2271) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2271.1, data_12_2271.2]

/-- Complete interval computation for depth 12, residue 2272. -/
theorem bounds_12_2272 : exactInterval 12 2272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2272 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2272) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2272 : oddCount 2272 12 = 5 ∧ acceleratedOrbit 12 2272 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2272 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2272) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2272.1, data_12_2272.2]

end Collatz.Research.StoppingAtlas.Batch0348
