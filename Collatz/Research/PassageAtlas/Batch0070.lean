import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0070

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2260. -/
theorem bounds_15_2260 : exactInterval 15 2260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2260 : oddCount 2260 15 = 3 ∧ acceleratedOrbit 15 2260 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2260) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2260.1, data_15_2260.2]

/-- Complete interval computation for depth 15, residue 2261. -/
theorem bounds_15_2261 : exactInterval 15 2261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2261 : oddCount 2261 15 = 3 ∧ acceleratedOrbit 15 2261 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2261) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2261.1, data_15_2261.2]

/-- Complete interval computation for depth 15, residue 2262. -/
theorem bounds_15_2262 : exactInterval 15 2262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2262 : oddCount 2262 15 = 8 ∧ acceleratedOrbit 15 2262 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2262) = 3 ^ 8 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2262.1, data_15_2262.2]

/-- Complete interval computation for depth 15, residue 2263. -/
theorem bounds_15_2263 : exactInterval 15 2263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2263 : oddCount 2263 15 = 8 ∧ acceleratedOrbit 15 2263 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2263) = 3 ^ 8 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2263.1, data_15_2263.2]

/-- Complete interval computation for depth 15, residue 2264. -/
theorem bounds_15_2264 : exactInterval 15 2264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2264 : oddCount 2264 15 = 9 ∧ acceleratedOrbit 15 2264 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2264) = 3 ^ 9 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2264.1, data_15_2264.2]

/-- Complete interval computation for depth 15, residue 2265. -/
theorem bounds_15_2265 : exactInterval 15 2265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2265 : oddCount 2265 15 = 9 ∧ acceleratedOrbit 15 2265 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2265) = 3 ^ 9 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2265.1, data_15_2265.2]

/-- Complete interval computation for depth 15, residue 2266. -/
theorem bounds_15_2266 : exactInterval 15 2266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2266 : oddCount 2266 15 = 9 ∧ acceleratedOrbit 15 2266 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2266) = 3 ^ 9 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2266.1, data_15_2266.2]

/-- Complete interval computation for depth 15, residue 2267. -/
theorem bounds_15_2267 : exactInterval 15 2267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2267 : oddCount 2267 15 = 10 ∧ acceleratedOrbit 15 2267 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2267) = 3 ^ 10 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2267.1, data_15_2267.2]

/-- Complete interval computation for depth 15, residue 2268. -/
theorem bounds_15_2268 : exactInterval 15 2268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2268 : oddCount 2268 15 = 9 ∧ acceleratedOrbit 15 2268 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2268) = 3 ^ 9 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2268.1, data_15_2268.2]

/-- Complete interval computation for depth 15, residue 2269. -/
theorem bounds_15_2269 : exactInterval 15 2269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2269 : oddCount 2269 15 = 9 ∧ acceleratedOrbit 15 2269 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2269) = 3 ^ 9 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2269.1, data_15_2269.2]

/-- Complete interval computation for depth 15, residue 2270. -/
theorem bounds_15_2270 : exactInterval 15 2270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2270 : oddCount 2270 15 = 8 ∧ acceleratedOrbit 15 2270 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2270) = 3 ^ 8 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2270.1, data_15_2270.2]

/-- Complete interval computation for depth 15, residue 2271. -/
theorem bounds_15_2271 : exactInterval 15 2271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2271 : oddCount 2271 15 = 8 ∧ acceleratedOrbit 15 2271 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2271) = 3 ^ 8 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2271.1, data_15_2271.2]

/-- Complete interval computation for depth 15, residue 2272. -/
theorem bounds_15_2272 : exactInterval 15 2272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2272 : oddCount 2272 15 = 7 ∧ acceleratedOrbit 15 2272 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2272) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2272.1, data_15_2272.2]

/-- Complete interval computation for depth 15, residue 2273. -/
theorem bounds_15_2273 : exactInterval 15 2273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2273 : oddCount 2273 15 = 11 ∧ acceleratedOrbit 15 2273 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2273) = 3 ^ 11 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2273.1, data_15_2273.2]

/-- Complete interval computation for depth 15, residue 2274. -/
theorem bounds_15_2274 : exactInterval 15 2274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2274 : oddCount 2274 15 = 3 ∧ acceleratedOrbit 15 2274 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2274) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2274.1, data_15_2274.2]

/-- Complete interval computation for depth 15, residue 2275. -/
theorem bounds_15_2275 : exactInterval 15 2275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2275 : oddCount 2275 15 = 3 ∧ acceleratedOrbit 15 2275 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2275) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2275.1, data_15_2275.2]

/-- Complete interval computation for depth 15, residue 2276. -/
theorem bounds_15_2276 : exactInterval 15 2276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2276 : oddCount 2276 15 = 9 ∧ acceleratedOrbit 15 2276 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2276) = 3 ^ 9 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2276.1, data_15_2276.2]

/-- Complete interval computation for depth 15, residue 2277. -/
theorem bounds_15_2277 : exactInterval 15 2277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2277 : oddCount 2277 15 = 9 ∧ acceleratedOrbit 15 2277 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2277) = 3 ^ 9 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2277.1, data_15_2277.2]

/-- Complete interval computation for depth 15, residue 2278. -/
theorem bounds_15_2278 : exactInterval 15 2278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2278 : oddCount 2278 15 = 9 ∧ acceleratedOrbit 15 2278 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2278) = 3 ^ 9 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2278.1, data_15_2278.2]

/-- Complete interval computation for depth 15, residue 2279. -/
theorem bounds_15_2279 : exactInterval 15 2279 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2279) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2279 : oddCount 2279 15 = 9 ∧ acceleratedOrbit 15 2279 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2279) = 3 ^ 9 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2279.1, data_15_2279.2]

/-- Complete interval computation for depth 15, residue 2280. -/
theorem bounds_15_2280 : exactInterval 15 2280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2280 : oddCount 2280 15 = 7 ∧ acceleratedOrbit 15 2280 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2280) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2280.1, data_15_2280.2]

/-- Complete interval computation for depth 15, residue 2281. -/
theorem bounds_15_2281 : exactInterval 15 2281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2281 : oddCount 2281 15 = 9 ∧ acceleratedOrbit 15 2281 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2281) = 3 ^ 9 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2281.1, data_15_2281.2]

/-- Complete interval computation for depth 15, residue 2282. -/
theorem bounds_15_2282 : exactInterval 15 2282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2282 : oddCount 2282 15 = 7 ∧ acceleratedOrbit 15 2282 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2282) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2282.1, data_15_2282.2]

/-- Complete interval computation for depth 15, residue 2283. -/
theorem bounds_15_2283 : exactInterval 15 2283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2283 : oddCount 2283 15 = 8 ∧ acceleratedOrbit 15 2283 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2283) = 3 ^ 8 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2283.1, data_15_2283.2]

/-- Complete interval computation for depth 15, residue 2284. -/
theorem bounds_15_2284 : exactInterval 15 2284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2284 : oddCount 2284 15 = 5 ∧ acceleratedOrbit 15 2284 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2284) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2284.1, data_15_2284.2]

/-- Complete interval computation for depth 15, residue 2285. -/
theorem bounds_15_2285 : exactInterval 15 2285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2285 : oddCount 2285 15 = 5 ∧ acceleratedOrbit 15 2285 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2285) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2285.1, data_15_2285.2]

/-- Complete interval computation for depth 15, residue 2286. -/
theorem bounds_15_2286 : exactInterval 15 2286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2286 : oddCount 2286 15 = 5 ∧ acceleratedOrbit 15 2286 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2286) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2286.1, data_15_2286.2]

/-- Complete interval computation for depth 15, residue 2287. -/
theorem bounds_15_2287 : exactInterval 15 2287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2287 : oddCount 2287 15 = 12 ∧ acceleratedOrbit 15 2287 = 37111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2287) = 3 ^ 12 * m + 37111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2287.1, data_15_2287.2]

/-- Complete interval computation for depth 15, residue 2288. -/
theorem bounds_15_2288 : exactInterval 15 2288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2288 : oddCount 2288 15 = 7 ∧ acceleratedOrbit 15 2288 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2288) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2288.1, data_15_2288.2]

/-- Complete interval computation for depth 15, residue 2289. -/
theorem bounds_15_2289 : exactInterval 15 2289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2289 : oddCount 2289 15 = 7 ∧ acceleratedOrbit 15 2289 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2289) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2289.1, data_15_2289.2]

/-- Complete interval computation for depth 15, residue 2290. -/
theorem bounds_15_2290 : exactInterval 15 2290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2290 : oddCount 2290 15 = 9 ∧ acceleratedOrbit 15 2290 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2290) = 3 ^ 9 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2290.1, data_15_2290.2]

/-- Complete interval computation for depth 15, residue 2291. -/
theorem bounds_15_2291 : exactInterval 15 2291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2291 : oddCount 2291 15 = 9 ∧ acceleratedOrbit 15 2291 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2291) = 3 ^ 9 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2291.1, data_15_2291.2]

/-- Complete interval computation for depth 15, residue 2292. -/
theorem bounds_15_2292 : exactInterval 15 2292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2292 : oddCount 2292 15 = 7 ∧ acceleratedOrbit 15 2292 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2292) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2292.1, data_15_2292.2]

end Collatz.Research.PassageAtlas.Batch0070
