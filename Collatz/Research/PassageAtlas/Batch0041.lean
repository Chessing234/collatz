import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0041

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1310. -/
theorem bounds_15_1310 : exactInterval 15 1310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1310 : oddCount 1310 15 = 10 ∧ acceleratedOrbit 15 1310 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1310) = 3 ^ 10 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1310.1, data_15_1310.2]

/-- Complete interval computation for depth 15, residue 1311. -/
theorem bounds_15_1311 : exactInterval 15 1311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1311 : oddCount 1311 15 = 8 ∧ acceleratedOrbit 15 1311 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1311) = 3 ^ 8 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1311.1, data_15_1311.2]

/-- Complete interval computation for depth 15, residue 1312. -/
theorem bounds_15_1312 : exactInterval 15 1312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1312 : oddCount 1312 15 = 7 ∧ acceleratedOrbit 15 1312 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1312) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1312.1, data_15_1312.2]

/-- Complete interval computation for depth 15, residue 1313. -/
theorem bounds_15_1313 : exactInterval 15 1313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1313 : oddCount 1313 15 = 5 ∧ acceleratedOrbit 15 1313 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1313) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1313.1, data_15_1313.2]

/-- Complete interval computation for depth 15, residue 1314. -/
theorem bounds_15_1314 : exactInterval 15 1314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1314 : oddCount 1314 15 = 7 ∧ acceleratedOrbit 15 1314 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1314) = 3 ^ 7 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1314.1, data_15_1314.2]

/-- Complete interval computation for depth 15, residue 1315. -/
theorem bounds_15_1315 : exactInterval 15 1315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1315 : oddCount 1315 15 = 7 ∧ acceleratedOrbit 15 1315 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1315) = 3 ^ 7 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1315.1, data_15_1315.2]

/-- Complete interval computation for depth 15, residue 1316. -/
theorem bounds_15_1316 : exactInterval 15 1316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1316 : oddCount 1316 15 = 7 ∧ acceleratedOrbit 15 1316 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1316) = 3 ^ 7 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1316.1, data_15_1316.2]

/-- Complete interval computation for depth 15, residue 1317. -/
theorem bounds_15_1317 : exactInterval 15 1317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1317 : oddCount 1317 15 = 7 ∧ acceleratedOrbit 15 1317 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1317) = 3 ^ 7 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1317.1, data_15_1317.2]

/-- Complete interval computation for depth 15, residue 1318. -/
theorem bounds_15_1318 : exactInterval 15 1318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1318 : oddCount 1318 15 = 7 ∧ acceleratedOrbit 15 1318 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1318) = 3 ^ 7 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1318.1, data_15_1318.2]

/-- Complete interval computation for depth 15, residue 1319. -/
theorem bounds_15_1319 : exactInterval 15 1319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1319 : oddCount 1319 15 = 8 ∧ acceleratedOrbit 15 1319 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1319) = 3 ^ 8 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1319.1, data_15_1319.2]

/-- Complete interval computation for depth 15, residue 1320. -/
theorem bounds_15_1320 : exactInterval 15 1320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1320 : oddCount 1320 15 = 7 ∧ acceleratedOrbit 15 1320 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1320) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1320.1, data_15_1320.2]

/-- Complete interval computation for depth 15, residue 1321. -/
theorem bounds_15_1321 : exactInterval 15 1321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1321 : oddCount 1321 15 = 11 ∧ acceleratedOrbit 15 1321 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1321) = 3 ^ 11 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1321.1, data_15_1321.2]

/-- Complete interval computation for depth 15, residue 1322. -/
theorem bounds_15_1322 : exactInterval 15 1322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1322 : oddCount 1322 15 = 7 ∧ acceleratedOrbit 15 1322 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1322) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1322.1, data_15_1322.2]

/-- Complete interval computation for depth 15, residue 1323. -/
theorem bounds_15_1323 : exactInterval 15 1323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1323 : oddCount 1323 15 = 7 ∧ acceleratedOrbit 15 1323 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1323) = 3 ^ 7 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1323.1, data_15_1323.2]

/-- Complete interval computation for depth 15, residue 1324. -/
theorem bounds_15_1324 : exactInterval 15 1324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1324 : oddCount 1324 15 = 5 ∧ acceleratedOrbit 15 1324 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1324) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1324.1, data_15_1324.2]

/-- Complete interval computation for depth 15, residue 1325. -/
theorem bounds_15_1325 : exactInterval 15 1325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1325 : oddCount 1325 15 = 5 ∧ acceleratedOrbit 15 1325 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1325) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1325.1, data_15_1325.2]

/-- Complete interval computation for depth 15, residue 1326. -/
theorem bounds_15_1326 : exactInterval 15 1326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1326 : oddCount 1326 15 = 5 ∧ acceleratedOrbit 15 1326 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1326) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1326.1, data_15_1326.2]

/-- Complete interval computation for depth 15, residue 1327. -/
theorem bounds_15_1327 : exactInterval 15 1327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1327 : oddCount 1327 15 = 8 ∧ acceleratedOrbit 15 1327 = 266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1327) = 3 ^ 8 * m + 266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1327.1, data_15_1327.2]

/-- Complete interval computation for depth 15, residue 1328. -/
theorem bounds_15_1328 : exactInterval 15 1328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1328 : oddCount 1328 15 = 7 ∧ acceleratedOrbit 15 1328 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1328) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1328.1, data_15_1328.2]

/-- Complete interval computation for depth 15, residue 1329. -/
theorem bounds_15_1329 : exactInterval 15 1329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1329 : oddCount 1329 15 = 8 ∧ acceleratedOrbit 15 1329 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1329) = 3 ^ 8 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1329.1, data_15_1329.2]

/-- Complete interval computation for depth 15, residue 1330. -/
theorem bounds_15_1330 : exactInterval 15 1330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1330 : oddCount 1330 15 = 8 ∧ acceleratedOrbit 15 1330 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1330) = 3 ^ 8 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1330.1, data_15_1330.2]

/-- Complete interval computation for depth 15, residue 1331. -/
theorem bounds_15_1331 : exactInterval 15 1331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1331 : oddCount 1331 15 = 8 ∧ acceleratedOrbit 15 1331 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1331) = 3 ^ 8 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1331.1, data_15_1331.2]

/-- Complete interval computation for depth 15, residue 1332. -/
theorem bounds_15_1332 : exactInterval 15 1332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1332 : oddCount 1332 15 = 7 ∧ acceleratedOrbit 15 1332 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1332) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1332.1, data_15_1332.2]

/-- Complete interval computation for depth 15, residue 1333. -/
theorem bounds_15_1333 : exactInterval 15 1333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1333 : oddCount 1333 15 = 7 ∧ acceleratedOrbit 15 1333 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1333) = 3 ^ 7 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1333.1, data_15_1333.2]

/-- Complete interval computation for depth 15, residue 1334. -/
theorem bounds_15_1334 : exactInterval 15 1334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1334 : oddCount 1334 15 = 11 ∧ acceleratedOrbit 15 1334 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1334) = 3 ^ 11 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1334.1, data_15_1334.2]

/-- Complete interval computation for depth 15, residue 1335. -/
theorem bounds_15_1335 : exactInterval 15 1335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1335 : oddCount 1335 15 = 11 ∧ acceleratedOrbit 15 1335 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1335) = 3 ^ 11 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1335.1, data_15_1335.2]

/-- Complete interval computation for depth 15, residue 1336. -/
theorem bounds_15_1336 : exactInterval 15 1336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1336 : oddCount 1336 15 = 10 ∧ acceleratedOrbit 15 1336 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1336) = 3 ^ 10 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1336.1, data_15_1336.2]

/-- Complete interval computation for depth 15, residue 1337. -/
theorem bounds_15_1337 : exactInterval 15 1337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1337 : oddCount 1337 15 = 9 ∧ acceleratedOrbit 15 1337 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1337) = 3 ^ 9 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1337.1, data_15_1337.2]

/-- Complete interval computation for depth 15, residue 1338. -/
theorem bounds_15_1338 : exactInterval 15 1338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1338 : oddCount 1338 15 = 10 ∧ acceleratedOrbit 15 1338 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1338) = 3 ^ 10 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1338.1, data_15_1338.2]

/-- Complete interval computation for depth 15, residue 1339. -/
theorem bounds_15_1339 : exactInterval 15 1339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1339 : oddCount 1339 15 = 5 ∧ acceleratedOrbit 15 1339 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1339) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1339.1, data_15_1339.2]

/-- Complete interval computation for depth 15, residue 1340. -/
theorem bounds_15_1340 : exactInterval 15 1340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1340 : oddCount 1340 15 = 10 ∧ acceleratedOrbit 15 1340 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1340) = 3 ^ 10 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1340.1, data_15_1340.2]

/-- Complete interval computation for depth 15, residue 1341. -/
theorem bounds_15_1341 : exactInterval 15 1341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1341 : oddCount 1341 15 = 10 ∧ acceleratedOrbit 15 1341 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1341) = 3 ^ 10 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1341.1, data_15_1341.2]

/-- Complete interval computation for depth 15, residue 1342. -/
theorem bounds_15_1342 : exactInterval 15 1342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1342 : oddCount 1342 15 = 10 ∧ acceleratedOrbit 15 1342 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1342) = 3 ^ 10 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1342.1, data_15_1342.2]

end Collatz.Research.PassageAtlas.Batch0041
