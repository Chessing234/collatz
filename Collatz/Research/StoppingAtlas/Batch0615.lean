import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0615

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2263. -/
theorem bounds_13_2263 : exactInterval 13 2263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2263 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2263) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2263 : oddCount 2263 13 = 7 ∧ acceleratedOrbit 13 2263 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2263 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2263) = 3 ^ 7 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2263.1, data_13_2263.2]

/-- Complete interval computation for depth 13, residue 2264. -/
theorem bounds_13_2264 : exactInterval 13 2264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2264 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2264) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2264 : oddCount 2264 13 = 8 ∧ acceleratedOrbit 13 2264 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2264 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2264) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2264.1, data_13_2264.2]

/-- Complete interval computation for depth 13, residue 2265. -/
theorem bounds_13_2265 : exactInterval 13 2265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2265 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2265) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2265 : oddCount 2265 13 = 7 ∧ acceleratedOrbit 13 2265 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2265 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2265) = 3 ^ 7 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2265.1, data_13_2265.2]

/-- Complete interval computation for depth 13, residue 2266. -/
theorem bounds_13_2266 : exactInterval 13 2266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2266 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2266) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2266 : oddCount 2266 13 = 8 ∧ acceleratedOrbit 13 2266 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2266 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2266) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2266.1, data_13_2266.2]

/-- Complete interval computation for depth 13, residue 2267. -/
theorem bounds_13_2267 : exactInterval 13 2267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2267 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2267) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2267 : oddCount 2267 13 = 9 ∧ acceleratedOrbit 13 2267 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2267 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2267) = 3 ^ 9 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2267.1, data_13_2267.2]

/-- Complete interval computation for depth 13, residue 2268. -/
theorem bounds_13_2268 : exactInterval 13 2268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2268 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2268) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2268 : oddCount 2268 13 = 8 ∧ acceleratedOrbit 13 2268 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2268 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2268) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2268.1, data_13_2268.2]

/-- Complete interval computation for depth 13, residue 2269. -/
theorem bounds_13_2269 : exactInterval 13 2269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2269 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2269) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2269 : oddCount 2269 13 = 8 ∧ acceleratedOrbit 13 2269 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2269 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2269) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2269.1, data_13_2269.2]

/-- Complete interval computation for depth 13, residue 2270. -/
theorem bounds_13_2270 : exactInterval 13 2270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2270 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2270) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2270 : oddCount 2270 13 = 8 ∧ acceleratedOrbit 13 2270 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2270 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2270) = 3 ^ 8 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2270.1, data_13_2270.2]

/-- Complete interval computation for depth 13, residue 2271. -/
theorem bounds_13_2271 : exactInterval 13 2271 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2271 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2271) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2271 : oddCount 2271 13 = 8 ∧ acceleratedOrbit 13 2271 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2271 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2271) = 3 ^ 8 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2271.1, data_13_2271.2]

/-- Complete interval computation for depth 13, residue 2272. -/
theorem bounds_13_2272 : exactInterval 13 2272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2272 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2272) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2272 : oddCount 2272 13 = 6 ∧ acceleratedOrbit 13 2272 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2272 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2272) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2272.1, data_13_2272.2]

/-- Complete interval computation for depth 13, residue 2273. -/
theorem bounds_13_2273 : exactInterval 13 2273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2273 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2273) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2273 : oddCount 2273 13 = 10 ∧ acceleratedOrbit 13 2273 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2273 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2273) = 3 ^ 10 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2273.1, data_13_2273.2]

/-- Complete interval computation for depth 13, residue 2274. -/
theorem bounds_13_2274 : exactInterval 13 2274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2274 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2274) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2274 : oddCount 2274 13 = 3 ∧ acceleratedOrbit 13 2274 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2274 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2274) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2274.1, data_13_2274.2]

/-- Complete interval computation for depth 13, residue 2275. -/
theorem bounds_13_2275 : exactInterval 13 2275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2275 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2275) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2275 : oddCount 2275 13 = 3 ∧ acceleratedOrbit 13 2275 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2275 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2275) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2275.1, data_13_2275.2]

/-- Complete interval computation for depth 13, residue 2276. -/
theorem bounds_13_2276 : exactInterval 13 2276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2276 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2276) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2276 : oddCount 2276 13 = 7 ∧ acceleratedOrbit 13 2276 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2276 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2276) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2276.1, data_13_2276.2]

/-- Complete interval computation for depth 13, residue 2277. -/
theorem bounds_13_2277 : exactInterval 13 2277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2277 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2277) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2277 : oddCount 2277 13 = 7 ∧ acceleratedOrbit 13 2277 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2277 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2277) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2277.1, data_13_2277.2]

end Collatz.Research.StoppingAtlas.Batch0615
