import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0747

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4290. -/
theorem bounds_13_4290 : exactInterval 13 4290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4290 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4290) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4290 : oddCount 4290 13 = 7 ∧ acceleratedOrbit 13 4290 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4290 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4290) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4290.1, data_13_4290.2]

/-- Complete interval computation for depth 13, residue 4291. -/
theorem bounds_13_4291 : exactInterval 13 4291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4291 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4291) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4291 : oddCount 4291 13 = 7 ∧ acceleratedOrbit 13 4291 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4291 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4291) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4291.1, data_13_4291.2]

/-- Complete interval computation for depth 13, residue 4292. -/
theorem bounds_13_4292 : exactInterval 13 4292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4292 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4292) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4292 : oddCount 4292 13 = 5 ∧ acceleratedOrbit 13 4292 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4292 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4292) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4292.1, data_13_4292.2]

/-- Complete interval computation for depth 13, residue 4293. -/
theorem bounds_13_4293 : exactInterval 13 4293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4293 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4293) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4293 : oddCount 4293 13 = 5 ∧ acceleratedOrbit 13 4293 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4293 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4293) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4293.1, data_13_4293.2]

/-- Complete interval computation for depth 13, residue 4294. -/
theorem bounds_13_4294 : exactInterval 13 4294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4294 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4294) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4294 : oddCount 4294 13 = 5 ∧ acceleratedOrbit 13 4294 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4294 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4294) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4294.1, data_13_4294.2]

/-- Complete interval computation for depth 13, residue 4295. -/
theorem bounds_13_4295 : exactInterval 13 4295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4295 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4295) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4295 : oddCount 4295 13 = 8 ∧ acceleratedOrbit 13 4295 = 3442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4295 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4295) = 3 ^ 8 * m + 3442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4295.1, data_13_4295.2]

/-- Complete interval computation for depth 13, residue 4296. -/
theorem bounds_13_4296 : exactInterval 13 4296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4296 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4296) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4296 : oddCount 4296 13 = 5 ∧ acceleratedOrbit 13 4296 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4296 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4296) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4296.1, data_13_4296.2]

/-- Complete interval computation for depth 13, residue 4297. -/
theorem bounds_13_4297 : exactInterval 13 4297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4297 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4297) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4297 : oddCount 4297 13 = 5 ∧ acceleratedOrbit 13 4297 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4297 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4297) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4297.1, data_13_4297.2]

/-- Complete interval computation for depth 13, residue 4298. -/
theorem bounds_13_4298 : exactInterval 13 4298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4298 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4298) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4298 : oddCount 4298 13 = 5 ∧ acceleratedOrbit 13 4298 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4298 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4298) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4298.1, data_13_4298.2]

/-- Complete interval computation for depth 13, residue 4299. -/
theorem bounds_13_4299 : exactInterval 13 4299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4299 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4299) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4299 : oddCount 4299 13 = 6 ∧ acceleratedOrbit 13 4299 = 383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4299 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4299) = 3 ^ 6 * m + 383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4299.1, data_13_4299.2]

/-- Complete interval computation for depth 13, residue 4300. -/
theorem bounds_13_4300 : exactInterval 13 4300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4300 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4300) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4300 : oddCount 4300 13 = 5 ∧ acceleratedOrbit 13 4300 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4300 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4300) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4300.1, data_13_4300.2]

/-- Complete interval computation for depth 13, residue 4301. -/
theorem bounds_13_4301 : exactInterval 13 4301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4301 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4301) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4301 : oddCount 4301 13 = 5 ∧ acceleratedOrbit 13 4301 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4301 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4301) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4301.1, data_13_4301.2]

/-- Complete interval computation for depth 13, residue 4302. -/
theorem bounds_13_4302 : exactInterval 13 4302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4302 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4302) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4302 : oddCount 4302 13 = 9 ∧ acceleratedOrbit 13 4302 = 10343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4302 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4302) = 3 ^ 9 * m + 10343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4302.1, data_13_4302.2]

/-- Complete interval computation for depth 13, residue 4303. -/
theorem bounds_13_4303 : exactInterval 13 4303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4303 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4303) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4303 : oddCount 4303 13 = 9 ∧ acceleratedOrbit 13 4303 = 10343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4303 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4303) = 3 ^ 9 * m + 10343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4303.1, data_13_4303.2]

/-- Complete interval computation for depth 13, residue 4304. -/
theorem bounds_13_4304 : exactInterval 13 4304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4304 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4304) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4304 : oddCount 4304 13 = 4 ∧ acceleratedOrbit 13 4304 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4304 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4304) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4304.1, data_13_4304.2]

end Collatz.Research.StoppingAtlas.Batch0747
