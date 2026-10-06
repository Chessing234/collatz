import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0315

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10289. -/
theorem bounds_15_10289 : exactInterval 15 10289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10289 : oddCount 10289 15 = 8 ∧ acceleratedOrbit 15 10289 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10289) = 3 ^ 8 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10289.1, data_15_10289.2]

/-- Complete interval computation for depth 15, residue 10290. -/
theorem bounds_15_10290 : exactInterval 15 10290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10290 : oddCount 10290 15 = 8 ∧ acceleratedOrbit 15 10290 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10290) = 3 ^ 8 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10290.1, data_15_10290.2]

/-- Complete interval computation for depth 15, residue 10291. -/
theorem bounds_15_10291 : exactInterval 15 10291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10291 : oddCount 10291 15 = 8 ∧ acceleratedOrbit 15 10291 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10291) = 3 ^ 8 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10291.1, data_15_10291.2]

/-- Complete interval computation for depth 15, residue 10292. -/
theorem bounds_15_10292 : exactInterval 15 10292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10292 : oddCount 10292 15 = 4 ∧ acceleratedOrbit 15 10292 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10292) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10292.1, data_15_10292.2]

/-- Complete interval computation for depth 15, residue 10293. -/
theorem bounds_15_10293 : exactInterval 15 10293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10293 : oddCount 10293 15 = 4 ∧ acceleratedOrbit 15 10293 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10293) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10293.1, data_15_10293.2]

/-- Complete interval computation for depth 15, residue 10294. -/
theorem bounds_15_10294 : exactInterval 15 10294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10294 : oddCount 10294 15 = 11 ∧ acceleratedOrbit 15 10294 = 55667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10294) = 3 ^ 11 * m + 55667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10294.1, data_15_10294.2]

/-- Complete interval computation for depth 15, residue 10295. -/
theorem bounds_15_10295 : exactInterval 15 10295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10295 : oddCount 10295 15 = 11 ∧ acceleratedOrbit 15 10295 = 55667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10295) = 3 ^ 11 * m + 55667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10295.1, data_15_10295.2]

/-- Complete interval computation for depth 15, residue 10296. -/
theorem bounds_15_10296 : exactInterval 15 10296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10296 : oddCount 10296 15 = 8 ∧ acceleratedOrbit 15 10296 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10296) = 3 ^ 8 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10296.1, data_15_10296.2]

/-- Complete interval computation for depth 15, residue 10297. -/
theorem bounds_15_10297 : exactInterval 15 10297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10297 : oddCount 10297 15 = 7 ∧ acceleratedOrbit 15 10297 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10297) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10297.1, data_15_10297.2]

/-- Complete interval computation for depth 15, residue 10298. -/
theorem bounds_15_10298 : exactInterval 15 10298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10298 : oddCount 10298 15 = 8 ∧ acceleratedOrbit 15 10298 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10298) = 3 ^ 8 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10298.1, data_15_10298.2]

/-- Complete interval computation for depth 15, residue 10299. -/
theorem bounds_15_10299 : exactInterval 15 10299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10299 : oddCount 10299 15 = 8 ∧ acceleratedOrbit 15 10299 = 2063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10299) = 3 ^ 8 * m + 2063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10299.1, data_15_10299.2]

/-- Complete interval computation for depth 15, residue 10300. -/
theorem bounds_15_10300 : exactInterval 15 10300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10300 : oddCount 10300 15 = 8 ∧ acceleratedOrbit 15 10300 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10300) = 3 ^ 8 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10300.1, data_15_10300.2]

/-- Complete interval computation for depth 15, residue 10301. -/
theorem bounds_15_10301 : exactInterval 15 10301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10301 : oddCount 10301 15 = 8 ∧ acceleratedOrbit 15 10301 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10301) = 3 ^ 8 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10301.1, data_15_10301.2]

/-- Complete interval computation for depth 15, residue 10302. -/
theorem bounds_15_10302 : exactInterval 15 10302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10302 : oddCount 10302 15 = 10 ∧ acceleratedOrbit 15 10302 = 18569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10302) = 3 ^ 10 * m + 18569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10302.1, data_15_10302.2]

/-- Complete interval computation for depth 15, residue 10303. -/
theorem bounds_15_10303 : exactInterval 15 10303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10303 : oddCount 10303 15 = 10 ∧ acceleratedOrbit 15 10303 = 18569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10303) = 3 ^ 10 * m + 18569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10303.1, data_15_10303.2]

/-- Complete interval computation for depth 15, residue 10304. -/
theorem bounds_15_10304 : exactInterval 15 10304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10304 : oddCount 10304 15 = 6 ∧ acceleratedOrbit 15 10304 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10304) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10304.1, data_15_10304.2]

/-- Complete interval computation for depth 15, residue 10305. -/
theorem bounds_15_10305 : exactInterval 15 10305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10305 : oddCount 10305 15 = 9 ∧ acceleratedOrbit 15 10305 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10305) = 3 ^ 9 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10305.1, data_15_10305.2]

/-- Complete interval computation for depth 15, residue 10306. -/
theorem bounds_15_10306 : exactInterval 15 10306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10306 : oddCount 10306 15 = 9 ∧ acceleratedOrbit 15 10306 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10306) = 3 ^ 9 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10306.1, data_15_10306.2]

/-- Complete interval computation for depth 15, residue 10307. -/
theorem bounds_15_10307 : exactInterval 15 10307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10307 : oddCount 10307 15 = 9 ∧ acceleratedOrbit 15 10307 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10307) = 3 ^ 9 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10307.1, data_15_10307.2]

/-- Complete interval computation for depth 15, residue 10308. -/
theorem bounds_15_10308 : exactInterval 15 10308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10308 : oddCount 10308 15 = 4 ∧ acceleratedOrbit 15 10308 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10308) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10308.1, data_15_10308.2]

/-- Complete interval computation for depth 15, residue 10309. -/
theorem bounds_15_10309 : exactInterval 15 10309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10309 : oddCount 10309 15 = 4 ∧ acceleratedOrbit 15 10309 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10309) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10309.1, data_15_10309.2]

/-- Complete interval computation for depth 15, residue 10310. -/
theorem bounds_15_10310 : exactInterval 15 10310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10310 : oddCount 10310 15 = 4 ∧ acceleratedOrbit 15 10310 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10310) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10310.1, data_15_10310.2]

/-- Complete interval computation for depth 15, residue 10311. -/
theorem bounds_15_10311 : exactInterval 15 10311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10311 : oddCount 10311 15 = 11 ∧ acceleratedOrbit 15 10311 = 55754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10311) = 3 ^ 11 * m + 55754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10311.1, data_15_10311.2]

/-- Complete interval computation for depth 15, residue 10312. -/
theorem bounds_15_10312 : exactInterval 15 10312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10312 : oddCount 10312 15 = 8 ∧ acceleratedOrbit 15 10312 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10312) = 3 ^ 8 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10312.1, data_15_10312.2]

/-- Complete interval computation for depth 15, residue 10313. -/
theorem bounds_15_10313 : exactInterval 15 10313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10313 : oddCount 10313 15 = 11 ∧ acceleratedOrbit 15 10313 = 55768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10313) = 3 ^ 11 * m + 55768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10313.1, data_15_10313.2]

/-- Complete interval computation for depth 15, residue 10314. -/
theorem bounds_15_10314 : exactInterval 15 10314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10314 : oddCount 10314 15 = 8 ∧ acceleratedOrbit 15 10314 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10314) = 3 ^ 8 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10314.1, data_15_10314.2]

/-- Complete interval computation for depth 15, residue 10315. -/
theorem bounds_15_10315 : exactInterval 15 10315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10315 : oddCount 10315 15 = 4 ∧ acceleratedOrbit 15 10315 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10315) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10315.1, data_15_10315.2]

/-- Complete interval computation for depth 15, residue 10316. -/
theorem bounds_15_10316 : exactInterval 15 10316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10316 : oddCount 10316 15 = 8 ∧ acceleratedOrbit 15 10316 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10316) = 3 ^ 8 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10316.1, data_15_10316.2]

/-- Complete interval computation for depth 15, residue 10317. -/
theorem bounds_15_10317 : exactInterval 15 10317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10317 : oddCount 10317 15 = 8 ∧ acceleratedOrbit 15 10317 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10317) = 3 ^ 8 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10317.1, data_15_10317.2]

/-- Complete interval computation for depth 15, residue 10318. -/
theorem bounds_15_10318 : exactInterval 15 10318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10318 : oddCount 10318 15 = 7 ∧ acceleratedOrbit 15 10318 = 689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10318) = 3 ^ 7 * m + 689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10318.1, data_15_10318.2]

/-- Complete interval computation for depth 15, residue 10319. -/
theorem bounds_15_10319 : exactInterval 15 10319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10319 : oddCount 10319 15 = 7 ∧ acceleratedOrbit 15 10319 = 689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10319) = 3 ^ 7 * m + 689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10319.1, data_15_10319.2]

/-- Complete interval computation for depth 15, residue 10320. -/
theorem bounds_15_10320 : exactInterval 15 10320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10320 : oddCount 10320 15 = 6 ∧ acceleratedOrbit 15 10320 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10320) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10320.1, data_15_10320.2]

end Collatz.Research.PassageAtlas.Batch0315
