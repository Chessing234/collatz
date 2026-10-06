import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0153

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1310. -/
theorem bounds_11_1310 : exactInterval 11 1310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1310 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1310) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1310 : oddCount 1310 11 = 7 ∧ acceleratedOrbit 11 1310 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1310 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1310) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1310.1, data_11_1310.2]

/-- Complete interval computation for depth 11, residue 1311. -/
theorem bounds_11_1311 : exactInterval 11 1311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1311 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1311) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1311 : oddCount 1311 11 = 6 ∧ acceleratedOrbit 11 1311 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1311 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1311) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1311.1, data_11_1311.2]

/-- Complete interval computation for depth 11, residue 1312. -/
theorem bounds_11_1312 : exactInterval 11 1312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1312 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1312) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1312 : oddCount 1312 11 = 5 ∧ acceleratedOrbit 11 1312 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1312 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1312) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1312.1, data_11_1312.2]

/-- Complete interval computation for depth 11, residue 1313. -/
theorem bounds_11_1313 : exactInterval 11 1313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1313 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1313) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1313 : oddCount 1313 11 = 4 ∧ acceleratedOrbit 11 1313 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1313 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1313) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1313.1, data_11_1313.2]

/-- Complete interval computation for depth 11, residue 1314. -/
theorem bounds_11_1314 : exactInterval 11 1314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1314 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1314) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1314 : oddCount 1314 11 = 5 ∧ acceleratedOrbit 11 1314 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1314 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1314) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1314.1, data_11_1314.2]

/-- Complete interval computation for depth 11, residue 1315. -/
theorem bounds_11_1315 : exactInterval 11 1315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1315 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1315) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1315 : oddCount 1315 11 = 5 ∧ acceleratedOrbit 11 1315 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1315 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1315) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1315.1, data_11_1315.2]

/-- Complete interval computation for depth 11, residue 1316. -/
theorem bounds_11_1316 : exactInterval 11 1316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1316 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1316) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1316 : oddCount 1316 11 = 5 ∧ acceleratedOrbit 11 1316 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1316 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1316) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1316.1, data_11_1316.2]

/-- Complete interval computation for depth 11, residue 1317. -/
theorem bounds_11_1317 : exactInterval 11 1317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1317 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1317) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1317 : oddCount 1317 11 = 5 ∧ acceleratedOrbit 11 1317 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1317 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1317) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1317.1, data_11_1317.2]

/-- Complete interval computation for depth 11, residue 1318. -/
theorem bounds_11_1318 : exactInterval 11 1318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1318 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1318) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1318 : oddCount 1318 11 = 5 ∧ acceleratedOrbit 11 1318 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1318 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1318) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1318.1, data_11_1318.2]

/-- Complete interval computation for depth 11, residue 1319. -/
theorem bounds_11_1319 : exactInterval 11 1319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1319 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1319) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1319 : oddCount 1319 11 = 6 ∧ acceleratedOrbit 11 1319 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1319 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1319) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1319.1, data_11_1319.2]

/-- Complete interval computation for depth 11, residue 1320. -/
theorem bounds_11_1320 : exactInterval 11 1320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1320 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1320) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1320 : oddCount 1320 11 = 5 ∧ acceleratedOrbit 11 1320 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1320 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1320) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1320.1, data_11_1320.2]

/-- Complete interval computation for depth 11, residue 1321. -/
theorem bounds_11_1321 : exactInterval 11 1321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1321 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1321) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1321 : oddCount 1321 11 = 8 ∧ acceleratedOrbit 11 1321 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1321 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1321) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1321.1, data_11_1321.2]

/-- Complete interval computation for depth 11, residue 1322. -/
theorem bounds_11_1322 : exactInterval 11 1322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1322 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1322) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1322 : oddCount 1322 11 = 5 ∧ acceleratedOrbit 11 1322 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1322 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1322) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1322.1, data_11_1322.2]

/-- Complete interval computation for depth 11, residue 1323. -/
theorem bounds_11_1323 : exactInterval 11 1323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1323 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1323) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1323 : oddCount 1323 11 = 6 ∧ acceleratedOrbit 11 1323 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1323 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1323) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1323.1, data_11_1323.2]

/-- Complete interval computation for depth 11, residue 1324. -/
theorem bounds_11_1324 : exactInterval 11 1324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1324 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1324) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1324 : oddCount 1324 11 = 4 ∧ acceleratedOrbit 11 1324 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1324 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1324) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1324.1, data_11_1324.2]

/-- Complete interval computation for depth 11, residue 1325. -/
theorem bounds_11_1325 : exactInterval 11 1325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1325 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1325) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1325 : oddCount 1325 11 = 4 ∧ acceleratedOrbit 11 1325 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1325 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1325) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1325.1, data_11_1325.2]

end Collatz.Research.StoppingAtlas.Batch0153
