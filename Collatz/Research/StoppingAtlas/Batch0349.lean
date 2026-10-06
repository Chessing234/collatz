import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0349

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2273. -/
theorem bounds_12_2273 : exactInterval 12 2273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2273 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2273) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2273 : oddCount 2273 12 = 10 ∧ acceleratedOrbit 12 2273 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2273 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2273) = 3 ^ 10 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2273.1, data_12_2273.2]

/-- Complete interval computation for depth 12, residue 2274. -/
theorem bounds_12_2274 : exactInterval 12 2274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2274 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2274) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2274 : oddCount 2274 12 = 2 ∧ acceleratedOrbit 12 2274 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2274 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2274) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2274.1, data_12_2274.2]

/-- Complete interval computation for depth 12, residue 2275. -/
theorem bounds_12_2275 : exactInterval 12 2275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2275 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2275) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2275 : oddCount 2275 12 = 2 ∧ acceleratedOrbit 12 2275 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2275 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2275) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2275.1, data_12_2275.2]

/-- Complete interval computation for depth 12, residue 2276. -/
theorem bounds_12_2276 : exactInterval 12 2276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2276 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2276) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2276 : oddCount 2276 12 = 6 ∧ acceleratedOrbit 12 2276 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2276 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2276) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2276.1, data_12_2276.2]

/-- Complete interval computation for depth 12, residue 2277. -/
theorem bounds_12_2277 : exactInterval 12 2277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2277 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2277) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2277 : oddCount 2277 12 = 6 ∧ acceleratedOrbit 12 2277 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2277 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2277) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2277.1, data_12_2277.2]

/-- Complete interval computation for depth 12, residue 2278. -/
theorem bounds_12_2278 : exactInterval 12 2278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2278 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2278) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2278 : oddCount 2278 12 = 6 ∧ acceleratedOrbit 12 2278 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2278 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2278) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2278.1, data_12_2278.2]

/-- Complete interval computation for depth 12, residue 2279. -/
theorem bounds_12_2279 : exactInterval 12 2279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2279 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2279) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2279 : oddCount 2279 12 = 8 ∧ acceleratedOrbit 12 2279 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2279 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2279) = 3 ^ 8 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2279.1, data_12_2279.2]

/-- Complete interval computation for depth 12, residue 2280. -/
theorem bounds_12_2280 : exactInterval 12 2280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2280 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2280) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2280 : oddCount 2280 12 = 5 ∧ acceleratedOrbit 12 2280 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2280 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2280) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2280.1, data_12_2280.2]

/-- Complete interval computation for depth 12, residue 2281. -/
theorem bounds_12_2281 : exactInterval 12 2281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2281 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2281) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2281 : oddCount 2281 12 = 7 ∧ acceleratedOrbit 12 2281 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2281 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2281) = 3 ^ 7 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2281.1, data_12_2281.2]

/-- Complete interval computation for depth 12, residue 2282. -/
theorem bounds_12_2282 : exactInterval 12 2282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2282 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2282) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2282 : oddCount 2282 12 = 5 ∧ acceleratedOrbit 12 2282 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2282 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2282) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2282.1, data_12_2282.2]

/-- Complete interval computation for depth 12, residue 2283. -/
theorem bounds_12_2283 : exactInterval 12 2283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2283 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2283) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2283 : oddCount 2283 12 = 7 ∧ acceleratedOrbit 12 2283 = 1220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2283 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2283) = 3 ^ 7 * m + 1220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2283.1, data_12_2283.2]

/-- Complete interval computation for depth 12, residue 2284. -/
theorem bounds_12_2284 : exactInterval 12 2284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2284 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2284) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2284 : oddCount 2284 12 = 5 ∧ acceleratedOrbit 12 2284 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2284 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2284) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2284.1, data_12_2284.2]

/-- Complete interval computation for depth 12, residue 2285. -/
theorem bounds_12_2285 : exactInterval 12 2285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2285 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2285) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2285 : oddCount 2285 12 = 5 ∧ acceleratedOrbit 12 2285 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2285 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2285) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2285.1, data_12_2285.2]

/-- Complete interval computation for depth 12, residue 2286. -/
theorem bounds_12_2286 : exactInterval 12 2286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2286 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2286) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2286 : oddCount 2286 12 = 5 ∧ acceleratedOrbit 12 2286 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2286 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2286) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2286.1, data_12_2286.2]

/-- Complete interval computation for depth 12, residue 2287. -/
theorem bounds_12_2287 : exactInterval 12 2287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2287 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2287) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2287 : oddCount 2287 12 = 10 ∧ acceleratedOrbit 12 2287 = 32987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2287 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2287) = 3 ^ 10 * m + 32987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2287.1, data_12_2287.2]

end Collatz.Research.StoppingAtlas.Batch0349
