import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0877

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6287. -/
theorem bounds_13_6287 : exactInterval 13 6287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6287 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6287) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6287 : oddCount 6287 13 = 7 ∧ acceleratedOrbit 13 6287 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6287 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6287) = 3 ^ 7 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6287.1, data_13_6287.2]

/-- Complete interval computation for depth 13, residue 6288. -/
theorem bounds_13_6288 : exactInterval 13 6288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6288 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6288) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6288 : oddCount 6288 13 = 6 ∧ acceleratedOrbit 13 6288 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6288 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6288) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6288.1, data_13_6288.2]

/-- Complete interval computation for depth 13, residue 6289. -/
theorem bounds_13_6289 : exactInterval 13 6289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6289 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6289) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6289 : oddCount 6289 13 = 8 ∧ acceleratedOrbit 13 6289 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6289 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6289) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6289.1, data_13_6289.2]

/-- Complete interval computation for depth 13, residue 6290. -/
theorem bounds_13_6290 : exactInterval 13 6290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6290 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6290) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6290 : oddCount 6290 13 = 8 ∧ acceleratedOrbit 13 6290 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6290 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6290) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6290.1, data_13_6290.2]

/-- Complete interval computation for depth 13, residue 6291. -/
theorem bounds_13_6291 : exactInterval 13 6291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6291 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6291) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6291 : oddCount 6291 13 = 8 ∧ acceleratedOrbit 13 6291 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6291 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6291) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6291.1, data_13_6291.2]

/-- Complete interval computation for depth 13, residue 6292. -/
theorem bounds_13_6292 : exactInterval 13 6292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6292 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6292) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6292 : oddCount 6292 13 = 6 ∧ acceleratedOrbit 13 6292 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6292 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6292) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6292.1, data_13_6292.2]

/-- Complete interval computation for depth 13, residue 6293. -/
theorem bounds_13_6293 : exactInterval 13 6293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6293 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6293) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6293 : oddCount 6293 13 = 6 ∧ acceleratedOrbit 13 6293 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6293 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6293) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6293.1, data_13_6293.2]

/-- Complete interval computation for depth 13, residue 6294. -/
theorem bounds_13_6294 : exactInterval 13 6294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6294 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6294) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6294 : oddCount 6294 13 = 5 ∧ acceleratedOrbit 13 6294 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6294 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6294) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6294.1, data_13_6294.2]

/-- Complete interval computation for depth 13, residue 6295. -/
theorem bounds_13_6295 : exactInterval 13 6295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6295 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6295) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6295 : oddCount 6295 13 = 5 ∧ acceleratedOrbit 13 6295 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6295 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6295) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6295.1, data_13_6295.2]

/-- Complete interval computation for depth 13, residue 6296. -/
theorem bounds_13_6296 : exactInterval 13 6296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6296 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6296) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6296 : oddCount 6296 13 = 6 ∧ acceleratedOrbit 13 6296 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6296 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6296) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6296.1, data_13_6296.2]

/-- Complete interval computation for depth 13, residue 6297. -/
theorem bounds_13_6297 : exactInterval 13 6297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6297 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6297) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6297 : oddCount 6297 13 = 8 ∧ acceleratedOrbit 13 6297 = 5048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6297 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6297) = 3 ^ 8 * m + 5048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6297.1, data_13_6297.2]

/-- Complete interval computation for depth 13, residue 6298. -/
theorem bounds_13_6298 : exactInterval 13 6298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6298 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6298) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6298 : oddCount 6298 13 = 6 ∧ acceleratedOrbit 13 6298 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6298 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6298) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6298.1, data_13_6298.2]

/-- Complete interval computation for depth 13, residue 6299. -/
theorem bounds_13_6299 : exactInterval 13 6299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6299 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6299) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6299 : oddCount 6299 13 = 7 ∧ acceleratedOrbit 13 6299 = 1682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6299 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6299) = 3 ^ 7 * m + 1682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6299.1, data_13_6299.2]

/-- Complete interval computation for depth 13, residue 6300. -/
theorem bounds_13_6300 : exactInterval 13 6300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6300 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6300) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6300 : oddCount 6300 13 = 5 ∧ acceleratedOrbit 13 6300 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6300 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6300) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6300.1, data_13_6300.2]

/-- Complete interval computation for depth 13, residue 6301. -/
theorem bounds_13_6301 : exactInterval 13 6301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6301 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6301) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6301 : oddCount 6301 13 = 5 ∧ acceleratedOrbit 13 6301 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6301 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6301) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6301.1, data_13_6301.2]

end Collatz.Research.StoppingAtlas.Batch0877
