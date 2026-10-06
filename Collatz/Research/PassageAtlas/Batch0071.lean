import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0071

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2293. -/
theorem bounds_15_2293 : exactInterval 15 2293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2293 : oddCount 2293 15 = 7 ∧ acceleratedOrbit 15 2293 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2293) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2293.1, data_15_2293.2]

/-- Complete interval computation for depth 15, residue 2294. -/
theorem bounds_15_2294 : exactInterval 15 2294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2294 : oddCount 2294 15 = 8 ∧ acceleratedOrbit 15 2294 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2294) = 3 ^ 8 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2294.1, data_15_2294.2]

/-- Complete interval computation for depth 15, residue 2295. -/
theorem bounds_15_2295 : exactInterval 15 2295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2295 : oddCount 2295 15 = 8 ∧ acceleratedOrbit 15 2295 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2295) = 3 ^ 8 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2295.1, data_15_2295.2]

/-- Complete interval computation for depth 15, residue 2296. -/
theorem bounds_15_2296 : exactInterval 15 2296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2296 : oddCount 2296 15 = 7 ∧ acceleratedOrbit 15 2296 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2296) = 3 ^ 7 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2296.1, data_15_2296.2]

/-- Complete interval computation for depth 15, residue 2297. -/
theorem bounds_15_2297 : exactInterval 15 2297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2297 : oddCount 2297 15 = 8 ∧ acceleratedOrbit 15 2297 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2297) = 3 ^ 8 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2297.1, data_15_2297.2]

/-- Complete interval computation for depth 15, residue 2298. -/
theorem bounds_15_2298 : exactInterval 15 2298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2298 : oddCount 2298 15 = 7 ∧ acceleratedOrbit 15 2298 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2298) = 3 ^ 7 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2298.1, data_15_2298.2]

/-- Complete interval computation for depth 15, residue 2299. -/
theorem bounds_15_2299 : exactInterval 15 2299 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2299) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2299 : oddCount 2299 15 = 9 ∧ acceleratedOrbit 15 2299 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2299) = 3 ^ 9 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2299.1, data_15_2299.2]

/-- Complete interval computation for depth 15, residue 2300. -/
theorem bounds_15_2300 : exactInterval 15 2300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2300 : oddCount 2300 15 = 7 ∧ acceleratedOrbit 15 2300 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2300) = 3 ^ 7 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2300.1, data_15_2300.2]

/-- Complete interval computation for depth 15, residue 2301. -/
theorem bounds_15_2301 : exactInterval 15 2301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2301 : oddCount 2301 15 = 7 ∧ acceleratedOrbit 15 2301 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2301) = 3 ^ 7 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2301.1, data_15_2301.2]

/-- Complete interval computation for depth 15, residue 2302. -/
theorem bounds_15_2302 : exactInterval 15 2302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2302 : oddCount 2302 15 = 9 ∧ acceleratedOrbit 15 2302 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2302) = 3 ^ 9 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2302.1, data_15_2302.2]

/-- Complete interval computation for depth 15, residue 2303. -/
theorem bounds_15_2303 : exactInterval 15 2303 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2303) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2303 : oddCount 2303 15 = 9 ∧ acceleratedOrbit 15 2303 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2303) = 3 ^ 9 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2303.1, data_15_2303.2]

/-- Complete interval computation for depth 15, residue 2304. -/
theorem bounds_15_2304 : exactInterval 15 2304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2304 : oddCount 2304 15 = 5 ∧ acceleratedOrbit 15 2304 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2304) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2304.1, data_15_2304.2]

/-- Complete interval computation for depth 15, residue 2305. -/
theorem bounds_15_2305 : exactInterval 15 2305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2305 : oddCount 2305 15 = 7 ∧ acceleratedOrbit 15 2305 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2305) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2305.1, data_15_2305.2]

/-- Complete interval computation for depth 15, residue 2306. -/
theorem bounds_15_2306 : exactInterval 15 2306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2306 : oddCount 2306 15 = 9 ∧ acceleratedOrbit 15 2306 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2306) = 3 ^ 9 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2306.1, data_15_2306.2]

/-- Complete interval computation for depth 15, residue 2307. -/
theorem bounds_15_2307 : exactInterval 15 2307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2307 : oddCount 2307 15 = 9 ∧ acceleratedOrbit 15 2307 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2307) = 3 ^ 9 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2307.1, data_15_2307.2]

/-- Complete interval computation for depth 15, residue 2308. -/
theorem bounds_15_2308 : exactInterval 15 2308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2308 : oddCount 2308 15 = 6 ∧ acceleratedOrbit 15 2308 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2308) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2308.1, data_15_2308.2]

/-- Complete interval computation for depth 15, residue 2309. -/
theorem bounds_15_2309 : exactInterval 15 2309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2309 : oddCount 2309 15 = 6 ∧ acceleratedOrbit 15 2309 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2309) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2309.1, data_15_2309.2]

/-- Complete interval computation for depth 15, residue 2310. -/
theorem bounds_15_2310 : exactInterval 15 2310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2310 : oddCount 2310 15 = 6 ∧ acceleratedOrbit 15 2310 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2310) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2310.1, data_15_2310.2]

/-- Complete interval computation for depth 15, residue 2311. -/
theorem bounds_15_2311 : exactInterval 15 2311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2311 : oddCount 2311 15 = 9 ∧ acceleratedOrbit 15 2311 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2311) = 3 ^ 9 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2311.1, data_15_2311.2]

/-- Complete interval computation for depth 15, residue 2312. -/
theorem bounds_15_2312 : exactInterval 15 2312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2312 : oddCount 2312 15 = 6 ∧ acceleratedOrbit 15 2312 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2312) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2312.1, data_15_2312.2]

/-- Complete interval computation for depth 15, residue 2313. -/
theorem bounds_15_2313 : exactInterval 15 2313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2313 : oddCount 2313 15 = 7 ∧ acceleratedOrbit 15 2313 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2313) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2313.1, data_15_2313.2]

/-- Complete interval computation for depth 15, residue 2314. -/
theorem bounds_15_2314 : exactInterval 15 2314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2314 : oddCount 2314 15 = 6 ∧ acceleratedOrbit 15 2314 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2314) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2314.1, data_15_2314.2]

/-- Complete interval computation for depth 15, residue 2315. -/
theorem bounds_15_2315 : exactInterval 15 2315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2315 : oddCount 2315 15 = 7 ∧ acceleratedOrbit 15 2315 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2315) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2315.1, data_15_2315.2]

/-- Complete interval computation for depth 15, residue 2316. -/
theorem bounds_15_2316 : exactInterval 15 2316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2316 : oddCount 2316 15 = 6 ∧ acceleratedOrbit 15 2316 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2316) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2316.1, data_15_2316.2]

/-- Complete interval computation for depth 15, residue 2317. -/
theorem bounds_15_2317 : exactInterval 15 2317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2317 : oddCount 2317 15 = 6 ∧ acceleratedOrbit 15 2317 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2317) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2317.1, data_15_2317.2]

/-- Complete interval computation for depth 15, residue 2318. -/
theorem bounds_15_2318 : exactInterval 15 2318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2318 : oddCount 2318 15 = 9 ∧ acceleratedOrbit 15 2318 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2318) = 3 ^ 9 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2318.1, data_15_2318.2]

/-- Complete interval computation for depth 15, residue 2319. -/
theorem bounds_15_2319 : exactInterval 15 2319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2319 : oddCount 2319 15 = 9 ∧ acceleratedOrbit 15 2319 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2319) = 3 ^ 9 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2319.1, data_15_2319.2]

/-- Complete interval computation for depth 15, residue 2320. -/
theorem bounds_15_2320 : exactInterval 15 2320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2320 : oddCount 2320 15 = 7 ∧ acceleratedOrbit 15 2320 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2320) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2320.1, data_15_2320.2]

/-- Complete interval computation for depth 15, residue 2321. -/
theorem bounds_15_2321 : exactInterval 15 2321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2321 : oddCount 2321 15 = 6 ∧ acceleratedOrbit 15 2321 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2321) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2321.1, data_15_2321.2]

/-- Complete interval computation for depth 15, residue 2322. -/
theorem bounds_15_2322 : exactInterval 15 2322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2322 : oddCount 2322 15 = 11 ∧ acceleratedOrbit 15 2322 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2322) = 3 ^ 11 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2322.1, data_15_2322.2]

/-- Complete interval computation for depth 15, residue 2323. -/
theorem bounds_15_2323 : exactInterval 15 2323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2323 : oddCount 2323 15 = 11 ∧ acceleratedOrbit 15 2323 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2323) = 3 ^ 11 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2323.1, data_15_2323.2]

/-- Complete interval computation for depth 15, residue 2324. -/
theorem bounds_15_2324 : exactInterval 15 2324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2324 : oddCount 2324 15 = 7 ∧ acceleratedOrbit 15 2324 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2324) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2324.1, data_15_2324.2]

/-- Complete interval computation for depth 15, residue 2325. -/
theorem bounds_15_2325 : exactInterval 15 2325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2325 : oddCount 2325 15 = 7 ∧ acceleratedOrbit 15 2325 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2325) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2325.1, data_15_2325.2]

end Collatz.Research.PassageAtlas.Batch0071
