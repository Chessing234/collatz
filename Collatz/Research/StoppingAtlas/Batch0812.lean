import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0812

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5288. -/
theorem bounds_13_5288 : exactInterval 13 5288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5288 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5288) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5288 : oddCount 5288 13 = 5 ∧ acceleratedOrbit 13 5288 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5288 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5288) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5288.1, data_13_5288.2]

/-- Complete interval computation for depth 13, residue 5289. -/
theorem bounds_13_5289 : exactInterval 13 5289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5289 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5289) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5289 : oddCount 5289 13 = 9 ∧ acceleratedOrbit 13 5289 = 12712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5289 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5289) = 3 ^ 9 * m + 12712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5289.1, data_13_5289.2]

/-- Complete interval computation for depth 13, residue 5290. -/
theorem bounds_13_5290 : exactInterval 13 5290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5290 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5290) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5290 : oddCount 5290 13 = 5 ∧ acceleratedOrbit 13 5290 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5290 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5290) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5290.1, data_13_5290.2]

/-- Complete interval computation for depth 13, residue 5291. -/
theorem bounds_13_5291 : exactInterval 13 5291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5291 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5291) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5291 : oddCount 5291 13 = 5 ∧ acceleratedOrbit 13 5291 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5291 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5291) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5291.1, data_13_5291.2]

/-- Complete interval computation for depth 13, residue 5292. -/
theorem bounds_13_5292 : exactInterval 13 5292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5292 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5292) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5292 : oddCount 5292 13 = 6 ∧ acceleratedOrbit 13 5292 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5292 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5292) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5292.1, data_13_5292.2]

/-- Complete interval computation for depth 13, residue 5293. -/
theorem bounds_13_5293 : exactInterval 13 5293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5293 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5293) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5293 : oddCount 5293 13 = 6 ∧ acceleratedOrbit 13 5293 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5293 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5293) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5293.1, data_13_5293.2]

/-- Complete interval computation for depth 13, residue 5294. -/
theorem bounds_13_5294 : exactInterval 13 5294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5294 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5294) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5294 : oddCount 5294 13 = 6 ∧ acceleratedOrbit 13 5294 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5294 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5294) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5294.1, data_13_5294.2]

/-- Complete interval computation for depth 13, residue 5295. -/
theorem bounds_13_5295 : exactInterval 13 5295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5295 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5295) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5295 : oddCount 5295 13 = 7 ∧ acceleratedOrbit 13 5295 = 1414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5295 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5295) = 3 ^ 7 * m + 1414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5295.1, data_13_5295.2]

/-- Complete interval computation for depth 13, residue 5296. -/
theorem bounds_13_5296 : exactInterval 13 5296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5296 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5296) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5296 : oddCount 5296 13 = 4 ∧ acceleratedOrbit 13 5296 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5296 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5296) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5296.1, data_13_5296.2]

/-- Complete interval computation for depth 13, residue 5297. -/
theorem bounds_13_5297 : exactInterval 13 5297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5297 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5297) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5297 : oddCount 5297 13 = 7 ∧ acceleratedOrbit 13 5297 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5297 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5297) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5297.1, data_13_5297.2]

/-- Complete interval computation for depth 13, residue 5298. -/
theorem bounds_13_5298 : exactInterval 13 5298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5298 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5298) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5298 : oddCount 5298 13 = 7 ∧ acceleratedOrbit 13 5298 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5298 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5298) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5298.1, data_13_5298.2]

/-- Complete interval computation for depth 13, residue 5299. -/
theorem bounds_13_5299 : exactInterval 13 5299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5299 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5299) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5299 : oddCount 5299 13 = 7 ∧ acceleratedOrbit 13 5299 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5299 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5299) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5299.1, data_13_5299.2]

/-- Complete interval computation for depth 13, residue 5300. -/
theorem bounds_13_5300 : exactInterval 13 5300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5300 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5300) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5300 : oddCount 5300 13 = 4 ∧ acceleratedOrbit 13 5300 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5300 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5300) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5300.1, data_13_5300.2]

/-- Complete interval computation for depth 13, residue 5301. -/
theorem bounds_13_5301 : exactInterval 13 5301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5301 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5301) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5301 : oddCount 5301 13 = 4 ∧ acceleratedOrbit 13 5301 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5301 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5301) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5301.1, data_13_5301.2]

/-- Complete interval computation for depth 13, residue 5302. -/
theorem bounds_13_5302 : exactInterval 13 5302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5302 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5302) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5302 : oddCount 5302 13 = 8 ∧ acceleratedOrbit 13 5302 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5302 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5302) = 3 ^ 8 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5302.1, data_13_5302.2]

/-- Complete interval computation for depth 13, residue 5303. -/
theorem bounds_13_5303 : exactInterval 13 5303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5303 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5303) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5303 : oddCount 5303 13 = 8 ∧ acceleratedOrbit 13 5303 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5303 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5303) = 3 ^ 8 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5303.1, data_13_5303.2]

end Collatz.Research.StoppingAtlas.Batch0812
