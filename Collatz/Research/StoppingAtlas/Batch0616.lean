import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0616

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2278. -/
theorem bounds_13_2278 : exactInterval 13 2278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2278 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2278) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2278 : oddCount 2278 13 = 7 ∧ acceleratedOrbit 13 2278 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2278 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2278) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2278.1, data_13_2278.2]

/-- Complete interval computation for depth 13, residue 2279. -/
theorem bounds_13_2279 : exactInterval 13 2279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2279 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2279) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2279 : oddCount 2279 13 = 9 ∧ acceleratedOrbit 13 2279 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2279 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2279) = 3 ^ 9 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2279.1, data_13_2279.2]

/-- Complete interval computation for depth 13, residue 2280. -/
theorem bounds_13_2280 : exactInterval 13 2280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2280 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2280) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2280 : oddCount 2280 13 = 6 ∧ acceleratedOrbit 13 2280 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2280 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2280) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2280.1, data_13_2280.2]

/-- Complete interval computation for depth 13, residue 2281. -/
theorem bounds_13_2281 : exactInterval 13 2281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2281 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2281) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2281 : oddCount 2281 13 = 8 ∧ acceleratedOrbit 13 2281 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2281 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2281) = 3 ^ 8 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2281.1, data_13_2281.2]

/-- Complete interval computation for depth 13, residue 2282. -/
theorem bounds_13_2282 : exactInterval 13 2282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2282 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2282) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2282 : oddCount 2282 13 = 6 ∧ acceleratedOrbit 13 2282 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2282 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2282) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2282.1, data_13_2282.2]

/-- Complete interval computation for depth 13, residue 2283. -/
theorem bounds_13_2283 : exactInterval 13 2283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2283 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2283) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2283 : oddCount 2283 13 = 7 ∧ acceleratedOrbit 13 2283 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2283 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2283) = 3 ^ 7 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2283.1, data_13_2283.2]

/-- Complete interval computation for depth 13, residue 2284. -/
theorem bounds_13_2284 : exactInterval 13 2284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2284 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2284) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2284 : oddCount 2284 13 = 5 ∧ acceleratedOrbit 13 2284 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2284 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2284) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2284.1, data_13_2284.2]

/-- Complete interval computation for depth 13, residue 2285. -/
theorem bounds_13_2285 : exactInterval 13 2285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2285 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2285) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2285 : oddCount 2285 13 = 5 ∧ acceleratedOrbit 13 2285 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2285 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2285) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2285.1, data_13_2285.2]

/-- Complete interval computation for depth 13, residue 2286. -/
theorem bounds_13_2286 : exactInterval 13 2286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2286 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2286) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2286 : oddCount 2286 13 = 5 ∧ acceleratedOrbit 13 2286 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2286 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2286) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2286.1, data_13_2286.2]

/-- Complete interval computation for depth 13, residue 2287. -/
theorem bounds_13_2287 : exactInterval 13 2287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2287 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2287) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2287 : oddCount 2287 13 = 11 ∧ acceleratedOrbit 13 2287 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2287 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2287) = 3 ^ 11 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2287.1, data_13_2287.2]

/-- Complete interval computation for depth 13, residue 2288. -/
theorem bounds_13_2288 : exactInterval 13 2288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2288 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2288) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2288 : oddCount 2288 13 = 6 ∧ acceleratedOrbit 13 2288 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2288 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2288) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2288.1, data_13_2288.2]

/-- Complete interval computation for depth 13, residue 2289. -/
theorem bounds_13_2289 : exactInterval 13 2289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2289 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2289) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2289 : oddCount 2289 13 = 6 ∧ acceleratedOrbit 13 2289 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2289 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2289) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2289.1, data_13_2289.2]

/-- Complete interval computation for depth 13, residue 2290. -/
theorem bounds_13_2290 : exactInterval 13 2290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2290 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2290) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2290 : oddCount 2290 13 = 8 ∧ acceleratedOrbit 13 2290 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2290 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2290) = 3 ^ 8 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2290.1, data_13_2290.2]

/-- Complete interval computation for depth 13, residue 2291. -/
theorem bounds_13_2291 : exactInterval 13 2291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2291 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2291) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2291 : oddCount 2291 13 = 8 ∧ acceleratedOrbit 13 2291 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2291 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2291) = 3 ^ 8 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2291.1, data_13_2291.2]

/-- Complete interval computation for depth 13, residue 2292. -/
theorem bounds_13_2292 : exactInterval 13 2292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2292 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2292) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2292 : oddCount 2292 13 = 6 ∧ acceleratedOrbit 13 2292 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2292 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2292) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2292.1, data_13_2292.2]

end Collatz.Research.StoppingAtlas.Batch0616
