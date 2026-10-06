import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0552

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1295. -/
theorem bounds_13_1295 : exactInterval 13 1295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1295 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1295) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1295 : oddCount 1295 13 = 6 ∧ acceleratedOrbit 13 1295 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1295 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1295) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1295.1, data_13_1295.2]

/-- Complete interval computation for depth 13, residue 1296. -/
theorem bounds_13_1296 : exactInterval 13 1296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1296 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1296) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1296 : oddCount 1296 13 = 5 ∧ acceleratedOrbit 13 1296 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1296 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1296) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1296.1, data_13_1296.2]

/-- Complete interval computation for depth 13, residue 1297. -/
theorem bounds_13_1297 : exactInterval 13 1297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1297 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1297) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1297 : oddCount 1297 13 = 7 ∧ acceleratedOrbit 13 1297 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1297 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1297) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1297.1, data_13_1297.2]

/-- Complete interval computation for depth 13, residue 1298. -/
theorem bounds_13_1298 : exactInterval 13 1298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1298 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1298) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1298 : oddCount 1298 13 = 8 ∧ acceleratedOrbit 13 1298 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1298 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1298) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1298.1, data_13_1298.2]

/-- Complete interval computation for depth 13, residue 1299. -/
theorem bounds_13_1299 : exactInterval 13 1299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1299 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1299) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1299 : oddCount 1299 13 = 8 ∧ acceleratedOrbit 13 1299 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1299 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1299) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1299.1, data_13_1299.2]

/-- Complete interval computation for depth 13, residue 1300. -/
theorem bounds_13_1300 : exactInterval 13 1300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1300 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1300) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1300 : oddCount 1300 13 = 5 ∧ acceleratedOrbit 13 1300 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1300 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1300) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1300.1, data_13_1300.2]

/-- Complete interval computation for depth 13, residue 1301. -/
theorem bounds_13_1301 : exactInterval 13 1301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1301 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1301) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1301 : oddCount 1301 13 = 5 ∧ acceleratedOrbit 13 1301 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1301 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1301) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1301.1, data_13_1301.2]

/-- Complete interval computation for depth 13, residue 1302. -/
theorem bounds_13_1302 : exactInterval 13 1302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1302 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1302) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1302 : oddCount 1302 13 = 7 ∧ acceleratedOrbit 13 1302 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1302 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1302) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1302.1, data_13_1302.2]

/-- Complete interval computation for depth 13, residue 1303. -/
theorem bounds_13_1303 : exactInterval 13 1303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1303 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1303) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1303 : oddCount 1303 13 = 7 ∧ acceleratedOrbit 13 1303 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1303 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1303) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1303.1, data_13_1303.2]

/-- Complete interval computation for depth 13, residue 1304. -/
theorem bounds_13_1304 : exactInterval 13 1304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1304 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1304) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1304 : oddCount 1304 13 = 5 ∧ acceleratedOrbit 13 1304 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1304 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1304) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1304.1, data_13_1304.2]

/-- Complete interval computation for depth 13, residue 1305. -/
theorem bounds_13_1305 : exactInterval 13 1305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1305 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1305) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1305 : oddCount 1305 13 = 8 ∧ acceleratedOrbit 13 1305 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1305 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1305) = 3 ^ 8 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1305.1, data_13_1305.2]

/-- Complete interval computation for depth 13, residue 1306. -/
theorem bounds_13_1306 : exactInterval 13 1306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1306 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1306) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1306 : oddCount 1306 13 = 5 ∧ acceleratedOrbit 13 1306 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1306 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1306) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1306.1, data_13_1306.2]

/-- Complete interval computation for depth 13, residue 1307. -/
theorem bounds_13_1307 : exactInterval 13 1307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1307 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1307) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1307 : oddCount 1307 13 = 11 ∧ acceleratedOrbit 13 1307 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1307 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1307) = 3 ^ 11 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1307.1, data_13_1307.2]

/-- Complete interval computation for depth 13, residue 1308. -/
theorem bounds_13_1308 : exactInterval 13 1308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1308 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1308) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1308 : oddCount 1308 13 = 9 ∧ acceleratedOrbit 13 1308 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1308 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1308) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1308.1, data_13_1308.2]

/-- Complete interval computation for depth 13, residue 1309. -/
theorem bounds_13_1309 : exactInterval 13 1309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1309 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1309) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1309 : oddCount 1309 13 = 9 ∧ acceleratedOrbit 13 1309 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1309 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1309) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1309.1, data_13_1309.2]

end Collatz.Research.StoppingAtlas.Batch0552
