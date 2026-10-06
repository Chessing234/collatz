import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0350

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2288. -/
theorem bounds_12_2288 : exactInterval 12 2288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2288 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2288) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2288 : oddCount 2288 12 = 5 ∧ acceleratedOrbit 12 2288 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2288 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2288) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2288.1, data_12_2288.2]

/-- Complete interval computation for depth 12, residue 2289. -/
theorem bounds_12_2289 : exactInterval 12 2289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2289 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2289) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2289 : oddCount 2289 12 = 5 ∧ acceleratedOrbit 12 2289 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2289 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2289) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2289.1, data_12_2289.2]

/-- Complete interval computation for depth 12, residue 2290. -/
theorem bounds_12_2290 : exactInterval 12 2290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2290 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2290) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2290 : oddCount 2290 12 = 7 ∧ acceleratedOrbit 12 2290 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2290 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2290) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2290.1, data_12_2290.2]

/-- Complete interval computation for depth 12, residue 2291. -/
theorem bounds_12_2291 : exactInterval 12 2291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2291 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2291) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2291 : oddCount 2291 12 = 7 ∧ acceleratedOrbit 12 2291 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2291 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2291) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2291.1, data_12_2291.2]

/-- Complete interval computation for depth 12, residue 2292. -/
theorem bounds_12_2292 : exactInterval 12 2292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2292 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2292) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2292 : oddCount 2292 12 = 5 ∧ acceleratedOrbit 12 2292 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2292 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2292) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2292.1, data_12_2292.2]

/-- Complete interval computation for depth 12, residue 2293. -/
theorem bounds_12_2293 : exactInterval 12 2293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2293 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2293) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2293 : oddCount 2293 12 = 5 ∧ acceleratedOrbit 12 2293 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2293 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2293) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2293.1, data_12_2293.2]

/-- Complete interval computation for depth 12, residue 2294. -/
theorem bounds_12_2294 : exactInterval 12 2294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2294 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2294) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2294 : oddCount 2294 12 = 6 ∧ acceleratedOrbit 12 2294 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2294 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2294) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2294.1, data_12_2294.2]

/-- Complete interval computation for depth 12, residue 2295. -/
theorem bounds_12_2295 : exactInterval 12 2295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2295 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2295) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2295 : oddCount 2295 12 = 6 ∧ acceleratedOrbit 12 2295 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2295 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2295) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2295.1, data_12_2295.2]

/-- Complete interval computation for depth 12, residue 2296. -/
theorem bounds_12_2296 : exactInterval 12 2296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2296 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2296) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2296 : oddCount 2296 12 = 6 ∧ acceleratedOrbit 12 2296 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2296 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2296) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2296.1, data_12_2296.2]

/-- Complete interval computation for depth 12, residue 2297. -/
theorem bounds_12_2297 : exactInterval 12 2297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2297 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2297) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2297 : oddCount 2297 12 = 7 ∧ acceleratedOrbit 12 2297 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2297 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2297) = 3 ^ 7 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2297.1, data_12_2297.2]

/-- Complete interval computation for depth 12, residue 2298. -/
theorem bounds_12_2298 : exactInterval 12 2298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2298 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2298) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2298 : oddCount 2298 12 = 6 ∧ acceleratedOrbit 12 2298 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2298 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2298) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2298.1, data_12_2298.2]

/-- Complete interval computation for depth 12, residue 2299. -/
theorem bounds_12_2299 : exactInterval 12 2299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2299 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2299) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2299 : oddCount 2299 12 = 9 ∧ acceleratedOrbit 12 2299 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2299 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2299) = 3 ^ 9 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2299.1, data_12_2299.2]

/-- Complete interval computation for depth 12, residue 2300. -/
theorem bounds_12_2300 : exactInterval 12 2300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2300 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2300) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2300 : oddCount 2300 12 = 6 ∧ acceleratedOrbit 12 2300 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2300 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2300) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2300.1, data_12_2300.2]

/-- Complete interval computation for depth 12, residue 2301. -/
theorem bounds_12_2301 : exactInterval 12 2301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2301 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2301) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2301 : oddCount 2301 12 = 6 ∧ acceleratedOrbit 12 2301 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2301 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2301) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2301.1, data_12_2301.2]

/-- Complete interval computation for depth 12, residue 2302. -/
theorem bounds_12_2302 : exactInterval 12 2302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2302 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2302) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2302 : oddCount 2302 12 = 9 ∧ acceleratedOrbit 12 2302 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2302 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2302) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2302.1, data_12_2302.2]

/-- Complete interval computation for depth 12, residue 2303. -/
theorem bounds_12_2303 : exactInterval 12 2303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2303 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2303) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2303 : oddCount 2303 12 = 9 ∧ acceleratedOrbit 12 2303 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2303 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2303) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2303.1, data_12_2303.2]

end Collatz.Research.StoppingAtlas.Batch0350
