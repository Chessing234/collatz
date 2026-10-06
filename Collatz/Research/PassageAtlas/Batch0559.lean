import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0559

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18284. -/
theorem bounds_15_18284 : exactInterval 15 18284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18284 : oddCount 18284 15 = 6 ∧ acceleratedOrbit 15 18284 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18284) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18284.1, data_15_18284.2]

/-- Complete interval computation for depth 15, residue 18285. -/
theorem bounds_15_18285 : exactInterval 15 18285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18285 : oddCount 18285 15 = 6 ∧ acceleratedOrbit 15 18285 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18285) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18285.1, data_15_18285.2]

/-- Complete interval computation for depth 15, residue 18286. -/
theorem bounds_15_18286 : exactInterval 15 18286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18286 : oddCount 18286 15 = 6 ∧ acceleratedOrbit 15 18286 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18286) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18286.1, data_15_18286.2]

/-- Complete interval computation for depth 15, residue 18287. -/
theorem bounds_15_18287 : exactInterval 15 18287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18287 : oddCount 18287 15 = 10 ∧ acceleratedOrbit 15 18287 = 32957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18287) = 3 ^ 10 * m + 32957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18287.1, data_15_18287.2]

/-- Complete interval computation for depth 15, residue 18288. -/
theorem bounds_15_18288 : exactInterval 15 18288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18288 : oddCount 18288 15 = 5 ∧ acceleratedOrbit 15 18288 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18288) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18288.1, data_15_18288.2]

/-- Complete interval computation for depth 15, residue 18289. -/
theorem bounds_15_18289 : exactInterval 15 18289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18289 : oddCount 18289 15 = 5 ∧ acceleratedOrbit 15 18289 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18289) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18289.1, data_15_18289.2]

/-- Complete interval computation for depth 15, residue 18290. -/
theorem bounds_15_18290 : exactInterval 15 18290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18290 : oddCount 18290 15 = 8 ∧ acceleratedOrbit 15 18290 = 3665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18290) = 3 ^ 8 * m + 3665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18290.1, data_15_18290.2]

/-- Complete interval computation for depth 15, residue 18291. -/
theorem bounds_15_18291 : exactInterval 15 18291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18291 : oddCount 18291 15 = 8 ∧ acceleratedOrbit 15 18291 = 3665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18291) = 3 ^ 8 * m + 3665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18291.1, data_15_18291.2]

/-- Complete interval computation for depth 15, residue 18292. -/
theorem bounds_15_18292 : exactInterval 15 18292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18292 : oddCount 18292 15 = 5 ∧ acceleratedOrbit 15 18292 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18292) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18292.1, data_15_18292.2]

/-- Complete interval computation for depth 15, residue 18293. -/
theorem bounds_15_18293 : exactInterval 15 18293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18293 : oddCount 18293 15 = 5 ∧ acceleratedOrbit 15 18293 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18293) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18293.1, data_15_18293.2]

/-- Complete interval computation for depth 15, residue 18294. -/
theorem bounds_15_18294 : exactInterval 15 18294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18294 : oddCount 18294 15 = 8 ∧ acceleratedOrbit 15 18294 = 3665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18294) = 3 ^ 8 * m + 3665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18294.1, data_15_18294.2]

/-- Complete interval computation for depth 15, residue 18295. -/
theorem bounds_15_18295 : exactInterval 15 18295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18295 : oddCount 18295 15 = 8 ∧ acceleratedOrbit 15 18295 = 3665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18295) = 3 ^ 8 * m + 3665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18295.1, data_15_18295.2]

/-- Complete interval computation for depth 15, residue 18296. -/
theorem bounds_15_18296 : exactInterval 15 18296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18296 : oddCount 18296 15 = 10 ∧ acceleratedOrbit 15 18296 = 32987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18296) = 3 ^ 10 * m + 32987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18296.1, data_15_18296.2]

/-- Complete interval computation for depth 15, residue 18297. -/
theorem bounds_15_18297 : exactInterval 15 18297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18297 : oddCount 18297 15 = 8 ∧ acceleratedOrbit 15 18297 = 3664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18297) = 3 ^ 8 * m + 3664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18297.1, data_15_18297.2]

/-- Complete interval computation for depth 15, residue 18298. -/
theorem bounds_15_18298 : exactInterval 15 18298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18298 : oddCount 18298 15 = 10 ∧ acceleratedOrbit 15 18298 = 32987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18298) = 3 ^ 10 * m + 32987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18298.1, data_15_18298.2]

/-- Complete interval computation for depth 15, residue 18299. -/
theorem bounds_15_18299 : exactInterval 15 18299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18299 : oddCount 18299 15 = 10 ∧ acceleratedOrbit 15 18299 = 32980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18299) = 3 ^ 10 * m + 32980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18299.1, data_15_18299.2]

/-- Complete interval computation for depth 15, residue 18300. -/
theorem bounds_15_18300 : exactInterval 15 18300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18300 : oddCount 18300 15 = 10 ∧ acceleratedOrbit 15 18300 = 32987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18300) = 3 ^ 10 * m + 32987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18300.1, data_15_18300.2]

/-- Complete interval computation for depth 15, residue 18301. -/
theorem bounds_15_18301 : exactInterval 15 18301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18301 : oddCount 18301 15 = 10 ∧ acceleratedOrbit 15 18301 = 32987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18301) = 3 ^ 10 * m + 32987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18301.1, data_15_18301.2]

/-- Complete interval computation for depth 15, residue 18302. -/
theorem bounds_15_18302 : exactInterval 15 18302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18302 : oddCount 18302 15 = 12 ∧ acceleratedOrbit 15 18302 = 296864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18302) = 3 ^ 12 * m + 296864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18302.1, data_15_18302.2]

/-- Complete interval computation for depth 15, residue 18303. -/
theorem bounds_15_18303 : exactInterval 15 18303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18303 : oddCount 18303 15 = 12 ∧ acceleratedOrbit 15 18303 = 296864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18303) = 3 ^ 12 * m + 296864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18303.1, data_15_18303.2]

/-- Complete interval computation for depth 15, residue 18304. -/
theorem bounds_15_18304 : exactInterval 15 18304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18304 : oddCount 18304 15 = 5 ∧ acceleratedOrbit 15 18304 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18304) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18304.1, data_15_18304.2]

/-- Complete interval computation for depth 15, residue 18305. -/
theorem bounds_15_18305 : exactInterval 15 18305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18305 : oddCount 18305 15 = 7 ∧ acceleratedOrbit 15 18305 = 1222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18305) = 3 ^ 7 * m + 1222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18305.1, data_15_18305.2]

/-- Complete interval computation for depth 15, residue 18306. -/
theorem bounds_15_18306 : exactInterval 15 18306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18306 : oddCount 18306 15 = 7 ∧ acceleratedOrbit 15 18306 = 1223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18306) = 3 ^ 7 * m + 1223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18306.1, data_15_18306.2]

/-- Complete interval computation for depth 15, residue 18307. -/
theorem bounds_15_18307 : exactInterval 15 18307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18307 : oddCount 18307 15 = 7 ∧ acceleratedOrbit 15 18307 = 1223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18307) = 3 ^ 7 * m + 1223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18307.1, data_15_18307.2]

/-- Complete interval computation for depth 15, residue 18308. -/
theorem bounds_15_18308 : exactInterval 15 18308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18308 : oddCount 18308 15 = 7 ∧ acceleratedOrbit 15 18308 = 1223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18308) = 3 ^ 7 * m + 1223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18308.1, data_15_18308.2]

/-- Complete interval computation for depth 15, residue 18309. -/
theorem bounds_15_18309 : exactInterval 15 18309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18309 : oddCount 18309 15 = 7 ∧ acceleratedOrbit 15 18309 = 1223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18309) = 3 ^ 7 * m + 1223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18309.1, data_15_18309.2]

/-- Complete interval computation for depth 15, residue 18310. -/
theorem bounds_15_18310 : exactInterval 15 18310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18310 : oddCount 18310 15 = 7 ∧ acceleratedOrbit 15 18310 = 1223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18310) = 3 ^ 7 * m + 1223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18310.1, data_15_18310.2]

/-- Complete interval computation for depth 15, residue 18311. -/
theorem bounds_15_18311 : exactInterval 15 18311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18311 : oddCount 18311 15 = 7 ∧ acceleratedOrbit 15 18311 = 1223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18311) = 3 ^ 7 * m + 1223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18311.1, data_15_18311.2]

/-- Complete interval computation for depth 15, residue 18312. -/
theorem bounds_15_18312 : exactInterval 15 18312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18312 : oddCount 18312 15 = 5 ∧ acceleratedOrbit 15 18312 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18312) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18312.1, data_15_18312.2]

/-- Complete interval computation for depth 15, residue 18313. -/
theorem bounds_15_18313 : exactInterval 15 18313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18313 : oddCount 18313 15 = 9 ∧ acceleratedOrbit 15 18313 = 11002 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18313) = 3 ^ 9 * m + 11002 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18313.1, data_15_18313.2]

/-- Complete interval computation for depth 15, residue 18314. -/
theorem bounds_15_18314 : exactInterval 15 18314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18314 : oddCount 18314 15 = 5 ∧ acceleratedOrbit 15 18314 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18314) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18314.1, data_15_18314.2]

/-- Complete interval computation for depth 15, residue 18315. -/
theorem bounds_15_18315 : exactInterval 15 18315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18315 : oddCount 18315 15 = 10 ∧ acceleratedOrbit 15 18315 = 33011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18315) = 3 ^ 10 * m + 33011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18315.1, data_15_18315.2]

/-- Complete interval computation for depth 15, residue 18316. -/
theorem bounds_15_18316 : exactInterval 15 18316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18316 : oddCount 18316 15 = 5 ∧ acceleratedOrbit 15 18316 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18316) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18316.1, data_15_18316.2]

end Collatz.Research.PassageAtlas.Batch0559
