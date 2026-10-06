import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0193

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6291. -/
theorem bounds_15_6291 : exactInterval 15 6291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6291 : oddCount 6291 15 = 9 ∧ acceleratedOrbit 15 6291 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6291) = 3 ^ 9 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6291.1, data_15_6291.2]

/-- Complete interval computation for depth 15, residue 6292. -/
theorem bounds_15_6292 : exactInterval 15 6292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6292 : oddCount 6292 15 = 7 ∧ acceleratedOrbit 15 6292 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6292) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6292.1, data_15_6292.2]

/-- Complete interval computation for depth 15, residue 6293. -/
theorem bounds_15_6293 : exactInterval 15 6293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6293 : oddCount 6293 15 = 7 ∧ acceleratedOrbit 15 6293 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6293) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6293.1, data_15_6293.2]

/-- Complete interval computation for depth 15, residue 6294. -/
theorem bounds_15_6294 : exactInterval 15 6294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6294 : oddCount 6294 15 = 5 ∧ acceleratedOrbit 15 6294 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6294) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6294.1, data_15_6294.2]

/-- Complete interval computation for depth 15, residue 6295. -/
theorem bounds_15_6295 : exactInterval 15 6295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6295 : oddCount 6295 15 = 5 ∧ acceleratedOrbit 15 6295 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6295) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6295.1, data_15_6295.2]

/-- Complete interval computation for depth 15, residue 6296. -/
theorem bounds_15_6296 : exactInterval 15 6296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6296 : oddCount 6296 15 = 7 ∧ acceleratedOrbit 15 6296 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6296) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6296.1, data_15_6296.2]

/-- Complete interval computation for depth 15, residue 6297. -/
theorem bounds_15_6297 : exactInterval 15 6297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6297 : oddCount 6297 15 = 8 ∧ acceleratedOrbit 15 6297 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6297) = 3 ^ 8 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6297.1, data_15_6297.2]

/-- Complete interval computation for depth 15, residue 6298. -/
theorem bounds_15_6298 : exactInterval 15 6298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6298 : oddCount 6298 15 = 7 ∧ acceleratedOrbit 15 6298 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6298) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6298.1, data_15_6298.2]

/-- Complete interval computation for depth 15, residue 6299. -/
theorem bounds_15_6299 : exactInterval 15 6299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6299 : oddCount 6299 15 = 8 ∧ acceleratedOrbit 15 6299 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6299) = 3 ^ 8 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6299.1, data_15_6299.2]

/-- Complete interval computation for depth 15, residue 6300. -/
theorem bounds_15_6300 : exactInterval 15 6300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6300 : oddCount 6300 15 = 7 ∧ acceleratedOrbit 15 6300 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6300) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6300.1, data_15_6300.2]

/-- Complete interval computation for depth 15, residue 6301. -/
theorem bounds_15_6301 : exactInterval 15 6301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6301 : oddCount 6301 15 = 7 ∧ acceleratedOrbit 15 6301 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6301) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6301.1, data_15_6301.2]

/-- Complete interval computation for depth 15, residue 6302. -/
theorem bounds_15_6302 : exactInterval 15 6302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6302 : oddCount 6302 15 = 7 ∧ acceleratedOrbit 15 6302 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6302) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6302.1, data_15_6302.2]

/-- Complete interval computation for depth 15, residue 6303. -/
theorem bounds_15_6303 : exactInterval 15 6303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6303 : oddCount 6303 15 = 12 ∧ acceleratedOrbit 15 6303 = 102242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6303) = 3 ^ 12 * m + 102242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6303.1, data_15_6303.2]

/-- Complete interval computation for depth 15, residue 6304. -/
theorem bounds_15_6304 : exactInterval 15 6304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6304 : oddCount 6304 15 = 4 ∧ acceleratedOrbit 15 6304 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6304) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6304.1, data_15_6304.2]

/-- Complete interval computation for depth 15, residue 6305. -/
theorem bounds_15_6305 : exactInterval 15 6305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6305 : oddCount 6305 15 = 7 ∧ acceleratedOrbit 15 6305 = 421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6305) = 3 ^ 7 * m + 421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6305.1, data_15_6305.2]

/-- Complete interval computation for depth 15, residue 6306. -/
theorem bounds_15_6306 : exactInterval 15 6306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6306 : oddCount 6306 15 = 7 ∧ acceleratedOrbit 15 6306 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6306) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6306.1, data_15_6306.2]

/-- Complete interval computation for depth 15, residue 6307. -/
theorem bounds_15_6307 : exactInterval 15 6307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6307 : oddCount 6307 15 = 7 ∧ acceleratedOrbit 15 6307 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6307) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6307.1, data_15_6307.2]

/-- Complete interval computation for depth 15, residue 6308. -/
theorem bounds_15_6308 : exactInterval 15 6308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6308 : oddCount 6308 15 = 10 ∧ acceleratedOrbit 15 6308 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6308) = 3 ^ 10 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6308.1, data_15_6308.2]

/-- Complete interval computation for depth 15, residue 6309. -/
theorem bounds_15_6309 : exactInterval 15 6309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6309 : oddCount 6309 15 = 10 ∧ acceleratedOrbit 15 6309 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6309) = 3 ^ 10 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6309.1, data_15_6309.2]

/-- Complete interval computation for depth 15, residue 6310. -/
theorem bounds_15_6310 : exactInterval 15 6310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6310 : oddCount 6310 15 = 10 ∧ acceleratedOrbit 15 6310 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6310) = 3 ^ 10 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6310.1, data_15_6310.2]

/-- Complete interval computation for depth 15, residue 6311. -/
theorem bounds_15_6311 : exactInterval 15 6311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6311 : oddCount 6311 15 = 11 ∧ acceleratedOrbit 15 6311 = 34127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6311) = 3 ^ 11 * m + 34127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6311.1, data_15_6311.2]

/-- Complete interval computation for depth 15, residue 6312. -/
theorem bounds_15_6312 : exactInterval 15 6312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6312 : oddCount 6312 15 = 4 ∧ acceleratedOrbit 15 6312 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6312) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6312.1, data_15_6312.2]

/-- Complete interval computation for depth 15, residue 6313. -/
theorem bounds_15_6313 : exactInterval 15 6313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6313 : oddCount 6313 15 = 11 ∧ acceleratedOrbit 15 6313 = 34138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6313) = 3 ^ 11 * m + 34138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6313.1, data_15_6313.2]

/-- Complete interval computation for depth 15, residue 6314. -/
theorem bounds_15_6314 : exactInterval 15 6314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6314 : oddCount 6314 15 = 4 ∧ acceleratedOrbit 15 6314 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6314) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6314.1, data_15_6314.2]

/-- Complete interval computation for depth 15, residue 6315. -/
theorem bounds_15_6315 : exactInterval 15 6315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6315 : oddCount 6315 15 = 9 ∧ acceleratedOrbit 15 6315 = 3797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6315) = 3 ^ 9 * m + 3797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6315.1, data_15_6315.2]

/-- Complete interval computation for depth 15, residue 6316. -/
theorem bounds_15_6316 : exactInterval 15 6316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6316 : oddCount 6316 15 = 5 ∧ acceleratedOrbit 15 6316 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6316) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6316.1, data_15_6316.2]

/-- Complete interval computation for depth 15, residue 6317. -/
theorem bounds_15_6317 : exactInterval 15 6317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6317 : oddCount 6317 15 = 5 ∧ acceleratedOrbit 15 6317 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6317) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6317.1, data_15_6317.2]

/-- Complete interval computation for depth 15, residue 6318. -/
theorem bounds_15_6318 : exactInterval 15 6318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6318 : oddCount 6318 15 = 5 ∧ acceleratedOrbit 15 6318 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6318) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6318.1, data_15_6318.2]

/-- Complete interval computation for depth 15, residue 6319. -/
theorem bounds_15_6319 : exactInterval 15 6319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6319 : oddCount 6319 15 = 11 ∧ acceleratedOrbit 15 6319 = 34172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6319) = 3 ^ 11 * m + 34172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6319.1, data_15_6319.2]

/-- Complete interval computation for depth 15, residue 6320. -/
theorem bounds_15_6320 : exactInterval 15 6320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6320 : oddCount 6320 15 = 7 ∧ acceleratedOrbit 15 6320 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6320) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6320.1, data_15_6320.2]

/-- Complete interval computation for depth 15, residue 6321. -/
theorem bounds_15_6321 : exactInterval 15 6321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6321 : oddCount 6321 15 = 9 ∧ acceleratedOrbit 15 6321 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6321) = 3 ^ 9 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6321.1, data_15_6321.2]

/-- Complete interval computation for depth 15, residue 6322. -/
theorem bounds_15_6322 : exactInterval 15 6322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6322 : oddCount 6322 15 = 9 ∧ acceleratedOrbit 15 6322 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6322) = 3 ^ 9 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6322.1, data_15_6322.2]

/-- Complete interval computation for depth 15, residue 6323. -/
theorem bounds_15_6323 : exactInterval 15 6323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6323 : oddCount 6323 15 = 9 ∧ acceleratedOrbit 15 6323 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6323) = 3 ^ 9 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6323.1, data_15_6323.2]

end Collatz.Research.PassageAtlas.Batch0193
