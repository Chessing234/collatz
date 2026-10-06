import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0285

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1290. -/
theorem bounds_12_1290 : exactInterval 12 1290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1290 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1290) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1290 : oddCount 1290 12 = 6 ∧ acceleratedOrbit 12 1290 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1290 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1290) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1290.1, data_12_1290.2]

/-- Complete interval computation for depth 12, residue 1291. -/
theorem bounds_12_1291 : exactInterval 12 1291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1291 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1291) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1291 : oddCount 1291 12 = 7 ∧ acceleratedOrbit 12 1291 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1291 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1291) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1291.1, data_12_1291.2]

/-- Complete interval computation for depth 12, residue 1292. -/
theorem bounds_12_1292 : exactInterval 12 1292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1292 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1292) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1292 : oddCount 1292 12 = 6 ∧ acceleratedOrbit 12 1292 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1292 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1292) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1292.1, data_12_1292.2]

/-- Complete interval computation for depth 12, residue 1293. -/
theorem bounds_12_1293 : exactInterval 12 1293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1293 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1293) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1293 : oddCount 1293 12 = 6 ∧ acceleratedOrbit 12 1293 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1293 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1293) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1293.1, data_12_1293.2]

/-- Complete interval computation for depth 12, residue 1294. -/
theorem bounds_12_1294 : exactInterval 12 1294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1294 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1294) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1294 : oddCount 1294 12 = 5 ∧ acceleratedOrbit 12 1294 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1294 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1294) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1294.1, data_12_1294.2]

/-- Complete interval computation for depth 12, residue 1295. -/
theorem bounds_12_1295 : exactInterval 12 1295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1295 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1295) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1295 : oddCount 1295 12 = 5 ∧ acceleratedOrbit 12 1295 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1295 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1295) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1295.1, data_12_1295.2]

/-- Complete interval computation for depth 12, residue 1296. -/
theorem bounds_12_1296 : exactInterval 12 1296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1296 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1296) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1296 : oddCount 1296 12 = 5 ∧ acceleratedOrbit 12 1296 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1296 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1296) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1296.1, data_12_1296.2]

/-- Complete interval computation for depth 12, residue 1297. -/
theorem bounds_12_1297 : exactInterval 12 1297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1297 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1297) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1297 : oddCount 1297 12 = 6 ∧ acceleratedOrbit 12 1297 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1297 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1297) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1297.1, data_12_1297.2]

/-- Complete interval computation for depth 12, residue 1298. -/
theorem bounds_12_1298 : exactInterval 12 1298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1298 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1298) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1298 : oddCount 1298 12 = 7 ∧ acceleratedOrbit 12 1298 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1298 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1298) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1298.1, data_12_1298.2]

/-- Complete interval computation for depth 12, residue 1299. -/
theorem bounds_12_1299 : exactInterval 12 1299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1299 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1299) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1299 : oddCount 1299 12 = 7 ∧ acceleratedOrbit 12 1299 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1299 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1299) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1299.1, data_12_1299.2]

/-- Complete interval computation for depth 12, residue 1300. -/
theorem bounds_12_1300 : exactInterval 12 1300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1300 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1300) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1300 : oddCount 1300 12 = 5 ∧ acceleratedOrbit 12 1300 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1300 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1300) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1300.1, data_12_1300.2]

/-- Complete interval computation for depth 12, residue 1301. -/
theorem bounds_12_1301 : exactInterval 12 1301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1301 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1301) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1301 : oddCount 1301 12 = 5 ∧ acceleratedOrbit 12 1301 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1301 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1301) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1301.1, data_12_1301.2]

/-- Complete interval computation for depth 12, residue 1302. -/
theorem bounds_12_1302 : exactInterval 12 1302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1302 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1302) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1302 : oddCount 1302 12 = 6 ∧ acceleratedOrbit 12 1302 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1302 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1302) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1302.1, data_12_1302.2]

/-- Complete interval computation for depth 12, residue 1303. -/
theorem bounds_12_1303 : exactInterval 12 1303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1303 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1303) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1303 : oddCount 1303 12 = 6 ∧ acceleratedOrbit 12 1303 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1303 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1303) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1303.1, data_12_1303.2]

/-- Complete interval computation for depth 12, residue 1304. -/
theorem bounds_12_1304 : exactInterval 12 1304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1304 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1304) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1304 : oddCount 1304 12 = 5 ∧ acceleratedOrbit 12 1304 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1304 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1304) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1304.1, data_12_1304.2]

end Collatz.Research.StoppingAtlas.Batch0285
