import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0617

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2293. -/
theorem bounds_13_2293 : exactInterval 13 2293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2293 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2293) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2293 : oddCount 2293 13 = 6 ∧ acceleratedOrbit 13 2293 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2293 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2293) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2293.1, data_13_2293.2]

/-- Complete interval computation for depth 13, residue 2294. -/
theorem bounds_13_2294 : exactInterval 13 2294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2294 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2294) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2294 : oddCount 2294 13 = 7 ∧ acceleratedOrbit 13 2294 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2294 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2294) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2294.1, data_13_2294.2]

/-- Complete interval computation for depth 13, residue 2295. -/
theorem bounds_13_2295 : exactInterval 13 2295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2295 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2295) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2295 : oddCount 2295 13 = 7 ∧ acceleratedOrbit 13 2295 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2295 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2295) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2295.1, data_13_2295.2]

/-- Complete interval computation for depth 13, residue 2296. -/
theorem bounds_13_2296 : exactInterval 13 2296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2296 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2296) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2296 : oddCount 2296 13 = 6 ∧ acceleratedOrbit 13 2296 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2296 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2296) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2296.1, data_13_2296.2]

/-- Complete interval computation for depth 13, residue 2297. -/
theorem bounds_13_2297 : exactInterval 13 2297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2297 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2297) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2297 : oddCount 2297 13 = 7 ∧ acceleratedOrbit 13 2297 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2297 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2297) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2297.1, data_13_2297.2]

/-- Complete interval computation for depth 13, residue 2298. -/
theorem bounds_13_2298 : exactInterval 13 2298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2298 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2298) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2298 : oddCount 2298 13 = 6 ∧ acceleratedOrbit 13 2298 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2298 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2298) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2298.1, data_13_2298.2]

/-- Complete interval computation for depth 13, residue 2299. -/
theorem bounds_13_2299 : exactInterval 13 2299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2299 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2299) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2299 : oddCount 2299 13 = 9 ∧ acceleratedOrbit 13 2299 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2299 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2299) = 3 ^ 9 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2299.1, data_13_2299.2]

/-- Complete interval computation for depth 13, residue 2300. -/
theorem bounds_13_2300 : exactInterval 13 2300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2300 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2300) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2300 : oddCount 2300 13 = 6 ∧ acceleratedOrbit 13 2300 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2300 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2300) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2300.1, data_13_2300.2]

/-- Complete interval computation for depth 13, residue 2301. -/
theorem bounds_13_2301 : exactInterval 13 2301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2301 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2301) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2301 : oddCount 2301 13 = 6 ∧ acceleratedOrbit 13 2301 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2301 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2301) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2301.1, data_13_2301.2]

/-- Complete interval computation for depth 13, residue 2302. -/
theorem bounds_13_2302 : exactInterval 13 2302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2302 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2302) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2302 : oddCount 2302 13 = 9 ∧ acceleratedOrbit 13 2302 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2302 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2302) = 3 ^ 9 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2302.1, data_13_2302.2]

/-- Complete interval computation for depth 13, residue 2303. -/
theorem bounds_13_2303 : exactInterval 13 2303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2303 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2303) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2303 : oddCount 2303 13 = 9 ∧ acceleratedOrbit 13 2303 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2303 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2303) = 3 ^ 9 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2303.1, data_13_2303.2]

/-- Complete interval computation for depth 13, residue 2304. -/
theorem bounds_13_2304 : exactInterval 13 2304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2304 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2304) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2304 : oddCount 2304 13 = 4 ∧ acceleratedOrbit 13 2304 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2304 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2304) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2304.1, data_13_2304.2]

/-- Complete interval computation for depth 13, residue 2305. -/
theorem bounds_13_2305 : exactInterval 13 2305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2305 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2305) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2305 : oddCount 2305 13 = 6 ∧ acceleratedOrbit 13 2305 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2305 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2305) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2305.1, data_13_2305.2]

/-- Complete interval computation for depth 13, residue 2306. -/
theorem bounds_13_2306 : exactInterval 13 2306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2306 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2306) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2306 : oddCount 2306 13 = 8 ∧ acceleratedOrbit 13 2306 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2306 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2306) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2306.1, data_13_2306.2]

/-- Complete interval computation for depth 13, residue 2307. -/
theorem bounds_13_2307 : exactInterval 13 2307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2307 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2307) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2307 : oddCount 2307 13 = 8 ∧ acceleratedOrbit 13 2307 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2307 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2307) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2307.1, data_13_2307.2]

/-- Complete interval computation for depth 13, residue 2308. -/
theorem bounds_13_2308 : exactInterval 13 2308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2308 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2308) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2308 : oddCount 2308 13 = 4 ∧ acceleratedOrbit 13 2308 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2308 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2308) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2308.1, data_13_2308.2]

end Collatz.Research.StoppingAtlas.Batch0617
