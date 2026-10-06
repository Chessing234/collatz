import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0942

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7285. -/
theorem bounds_13_7285 : exactInterval 13 7285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7285 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7285) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7285 : oddCount 7285 13 = 6 ∧ acceleratedOrbit 13 7285 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7285 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7285) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7285.1, data_13_7285.2]

/-- Complete interval computation for depth 13, residue 7286. -/
theorem bounds_13_7286 : exactInterval 13 7286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7286 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7286) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7286 : oddCount 7286 13 = 6 ∧ acceleratedOrbit 13 7286 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7286 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7286) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7286.1, data_13_7286.2]

/-- Complete interval computation for depth 13, residue 7287. -/
theorem bounds_13_7287 : exactInterval 13 7287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7287 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7287) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7287 : oddCount 7287 13 = 6 ∧ acceleratedOrbit 13 7287 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7287 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7287) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7287.1, data_13_7287.2]

/-- Complete interval computation for depth 13, residue 7288. -/
theorem bounds_13_7288 : exactInterval 13 7288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7288 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7288) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7288 : oddCount 7288 13 = 6 ∧ acceleratedOrbit 13 7288 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7288 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7288) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7288.1, data_13_7288.2]

/-- Complete interval computation for depth 13, residue 7289. -/
theorem bounds_13_7289 : exactInterval 13 7289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7289 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7289) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7289 : oddCount 7289 13 = 8 ∧ acceleratedOrbit 13 7289 = 5840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7289 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7289) = 3 ^ 8 * m + 5840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7289.1, data_13_7289.2]

/-- Complete interval computation for depth 13, residue 7290. -/
theorem bounds_13_7290 : exactInterval 13 7290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7290 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7290) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7290 : oddCount 7290 13 = 6 ∧ acceleratedOrbit 13 7290 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7290 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7290) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7290.1, data_13_7290.2]

/-- Complete interval computation for depth 13, residue 7291. -/
theorem bounds_13_7291 : exactInterval 13 7291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7291 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7291) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7291 : oddCount 7291 13 = 6 ∧ acceleratedOrbit 13 7291 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7291 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7291) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7291.1, data_13_7291.2]

/-- Complete interval computation for depth 13, residue 7292. -/
theorem bounds_13_7292 : exactInterval 13 7292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7292 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7292) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7292 : oddCount 7292 13 = 7 ∧ acceleratedOrbit 13 7292 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7292 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7292) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7292.1, data_13_7292.2]

/-- Complete interval computation for depth 13, residue 7293. -/
theorem bounds_13_7293 : exactInterval 13 7293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7293 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7293) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7293 : oddCount 7293 13 = 7 ∧ acceleratedOrbit 13 7293 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7293 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7293) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7293.1, data_13_7293.2]

/-- Complete interval computation for depth 13, residue 7294. -/
theorem bounds_13_7294 : exactInterval 13 7294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7294 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7294) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7294 : oddCount 7294 13 = 7 ∧ acceleratedOrbit 13 7294 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7294 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7294) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7294.1, data_13_7294.2]

/-- Complete interval computation for depth 13, residue 7295. -/
theorem bounds_13_7295 : exactInterval 13 7295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7295 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7295) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7295 : oddCount 7295 13 = 10 ∧ acceleratedOrbit 13 7295 = 52591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7295 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7295) = 3 ^ 10 * m + 52591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7295.1, data_13_7295.2]

/-- Complete interval computation for depth 13, residue 7296. -/
theorem bounds_13_7296 : exactInterval 13 7296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7296 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7296) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7296 : oddCount 7296 13 = 4 ∧ acceleratedOrbit 13 7296 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7296 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7296) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7296.1, data_13_7296.2]

/-- Complete interval computation for depth 13, residue 7297. -/
theorem bounds_13_7297 : exactInterval 13 7297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7297 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7297) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7297 : oddCount 7297 13 = 7 ∧ acceleratedOrbit 13 7297 = 1949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7297 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7297) = 3 ^ 7 * m + 1949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7297.1, data_13_7297.2]

/-- Complete interval computation for depth 13, residue 7298. -/
theorem bounds_13_7298 : exactInterval 13 7298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7298 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7298) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7298 : oddCount 7298 13 = 5 ∧ acceleratedOrbit 13 7298 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7298 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7298) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7298.1, data_13_7298.2]

/-- Complete interval computation for depth 13, residue 7299. -/
theorem bounds_13_7299 : exactInterval 13 7299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7299 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7299) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7299 : oddCount 7299 13 = 5 ∧ acceleratedOrbit 13 7299 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7299 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7299) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7299.1, data_13_7299.2]

/-- Complete interval computation for depth 13, residue 7300. -/
theorem bounds_13_7300 : exactInterval 13 7300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7300 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7300) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7300 : oddCount 7300 13 = 5 ∧ acceleratedOrbit 13 7300 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7300 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7300) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7300.1, data_13_7300.2]

end Collatz.Research.StoppingAtlas.Batch0942
