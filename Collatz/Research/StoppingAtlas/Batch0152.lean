import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0152

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1295. -/
theorem bounds_11_1295 : exactInterval 11 1295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1295 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1295) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1295 : oddCount 1295 11 = 5 ∧ acceleratedOrbit 11 1295 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1295 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1295) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1295.1, data_11_1295.2]

/-- Complete interval computation for depth 11, residue 1296. -/
theorem bounds_11_1296 : exactInterval 11 1296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1296 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1296) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1296 : oddCount 1296 11 = 4 ∧ acceleratedOrbit 11 1296 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1296 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1296) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1296.1, data_11_1296.2]

/-- Complete interval computation for depth 11, residue 1297. -/
theorem bounds_11_1297 : exactInterval 11 1297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1297 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1297) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1297 : oddCount 1297 11 = 5 ∧ acceleratedOrbit 11 1297 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1297 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1297) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1297.1, data_11_1297.2]

/-- Complete interval computation for depth 11, residue 1298. -/
theorem bounds_11_1298 : exactInterval 11 1298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1298 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1298) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1298 : oddCount 1298 11 = 7 ∧ acceleratedOrbit 11 1298 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1298 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1298) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1298.1, data_11_1298.2]

/-- Complete interval computation for depth 11, residue 1299. -/
theorem bounds_11_1299 : exactInterval 11 1299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1299 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1299) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1299 : oddCount 1299 11 = 7 ∧ acceleratedOrbit 11 1299 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1299 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1299) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1299.1, data_11_1299.2]

/-- Complete interval computation for depth 11, residue 1300. -/
theorem bounds_11_1300 : exactInterval 11 1300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1300 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1300) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1300 : oddCount 1300 11 = 4 ∧ acceleratedOrbit 11 1300 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1300 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1300) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1300.1, data_11_1300.2]

/-- Complete interval computation for depth 11, residue 1301. -/
theorem bounds_11_1301 : exactInterval 11 1301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1301 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1301) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1301 : oddCount 1301 11 = 4 ∧ acceleratedOrbit 11 1301 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1301 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1301) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1301.1, data_11_1301.2]

/-- Complete interval computation for depth 11, residue 1302. -/
theorem bounds_11_1302 : exactInterval 11 1302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1302 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1302) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1302 : oddCount 1302 11 = 5 ∧ acceleratedOrbit 11 1302 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1302 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1302) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1302.1, data_11_1302.2]

/-- Complete interval computation for depth 11, residue 1303. -/
theorem bounds_11_1303 : exactInterval 11 1303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1303 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1303) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1303 : oddCount 1303 11 = 5 ∧ acceleratedOrbit 11 1303 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1303 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1303) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1303.1, data_11_1303.2]

/-- Complete interval computation for depth 11, residue 1304. -/
theorem bounds_11_1304 : exactInterval 11 1304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1304 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1304) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1304 : oddCount 1304 11 = 4 ∧ acceleratedOrbit 11 1304 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1304 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1304) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1304.1, data_11_1304.2]

/-- Complete interval computation for depth 11, residue 1305. -/
theorem bounds_11_1305 : exactInterval 11 1305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1305 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1305) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1305 : oddCount 1305 11 = 7 ∧ acceleratedOrbit 11 1305 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1305 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1305) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1305.1, data_11_1305.2]

/-- Complete interval computation for depth 11, residue 1306. -/
theorem bounds_11_1306 : exactInterval 11 1306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1306 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1306) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1306 : oddCount 1306 11 = 4 ∧ acceleratedOrbit 11 1306 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1306 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1306) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1306.1, data_11_1306.2]

/-- Complete interval computation for depth 11, residue 1307. -/
theorem bounds_11_1307 : exactInterval 11 1307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1307 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1307) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1307 : oddCount 1307 11 = 9 ∧ acceleratedOrbit 11 1307 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1307 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1307) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1307.1, data_11_1307.2]

/-- Complete interval computation for depth 11, residue 1308. -/
theorem bounds_11_1308 : exactInterval 11 1308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1308 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1308) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1308 : oddCount 1308 11 = 7 ∧ acceleratedOrbit 11 1308 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1308 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1308) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1308.1, data_11_1308.2]

/-- Complete interval computation for depth 11, residue 1309. -/
theorem bounds_11_1309 : exactInterval 11 1309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1309 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1309) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1309 : oddCount 1309 11 = 7 ∧ acceleratedOrbit 11 1309 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1309 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1309) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1309.1, data_11_1309.2]

end Collatz.Research.StoppingAtlas.Batch0152
