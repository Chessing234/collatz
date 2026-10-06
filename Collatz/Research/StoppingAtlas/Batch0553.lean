import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0553

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1310. -/
theorem bounds_13_1310 : exactInterval 13 1310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1310 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1310) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1310 : oddCount 1310 13 = 9 ∧ acceleratedOrbit 13 1310 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1310 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1310) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1310.1, data_13_1310.2]

/-- Complete interval computation for depth 13, residue 1311. -/
theorem bounds_13_1311 : exactInterval 13 1311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1311 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1311) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1311 : oddCount 1311 13 = 8 ∧ acceleratedOrbit 13 1311 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1311 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1311) = 3 ^ 8 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1311.1, data_13_1311.2]

/-- Complete interval computation for depth 13, residue 1312. -/
theorem bounds_13_1312 : exactInterval 13 1312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1312 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1312) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1312 : oddCount 1312 13 = 6 ∧ acceleratedOrbit 13 1312 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1312 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1312) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1312.1, data_13_1312.2]

/-- Complete interval computation for depth 13, residue 1313. -/
theorem bounds_13_1313 : exactInterval 13 1313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1313 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1313) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1313 : oddCount 1313 13 = 4 ∧ acceleratedOrbit 13 1313 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1313 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1313) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1313.1, data_13_1313.2]

/-- Complete interval computation for depth 13, residue 1314. -/
theorem bounds_13_1314 : exactInterval 13 1314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1314 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1314) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1314 : oddCount 1314 13 = 6 ∧ acceleratedOrbit 13 1314 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1314 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1314) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1314.1, data_13_1314.2]

/-- Complete interval computation for depth 13, residue 1315. -/
theorem bounds_13_1315 : exactInterval 13 1315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1315 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1315) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1315 : oddCount 1315 13 = 6 ∧ acceleratedOrbit 13 1315 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1315 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1315) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1315.1, data_13_1315.2]

/-- Complete interval computation for depth 13, residue 1316. -/
theorem bounds_13_1316 : exactInterval 13 1316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1316 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1316) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1316 : oddCount 1316 13 = 6 ∧ acceleratedOrbit 13 1316 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1316 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1316) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1316.1, data_13_1316.2]

/-- Complete interval computation for depth 13, residue 1317. -/
theorem bounds_13_1317 : exactInterval 13 1317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1317 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1317) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1317 : oddCount 1317 13 = 6 ∧ acceleratedOrbit 13 1317 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1317 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1317) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1317.1, data_13_1317.2]

/-- Complete interval computation for depth 13, residue 1318. -/
theorem bounds_13_1318 : exactInterval 13 1318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1318 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1318) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1318 : oddCount 1318 13 = 6 ∧ acceleratedOrbit 13 1318 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1318 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1318) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1318.1, data_13_1318.2]

/-- Complete interval computation for depth 13, residue 1319. -/
theorem bounds_13_1319 : exactInterval 13 1319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1319 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1319) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1319 : oddCount 1319 13 = 7 ∧ acceleratedOrbit 13 1319 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1319 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1319) = 3 ^ 7 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1319.1, data_13_1319.2]

/-- Complete interval computation for depth 13, residue 1320. -/
theorem bounds_13_1320 : exactInterval 13 1320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1320 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1320) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1320 : oddCount 1320 13 = 6 ∧ acceleratedOrbit 13 1320 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1320 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1320) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1320.1, data_13_1320.2]

/-- Complete interval computation for depth 13, residue 1321. -/
theorem bounds_13_1321 : exactInterval 13 1321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1321 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1321) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1321 : oddCount 1321 13 = 9 ∧ acceleratedOrbit 13 1321 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1321 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1321) = 3 ^ 9 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1321.1, data_13_1321.2]

/-- Complete interval computation for depth 13, residue 1322. -/
theorem bounds_13_1322 : exactInterval 13 1322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1322 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1322) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1322 : oddCount 1322 13 = 6 ∧ acceleratedOrbit 13 1322 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1322 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1322) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1322.1, data_13_1322.2]

/-- Complete interval computation for depth 13, residue 1323. -/
theorem bounds_13_1323 : exactInterval 13 1323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1323 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1323) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1323 : oddCount 1323 13 = 6 ∧ acceleratedOrbit 13 1323 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1323 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1323) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1323.1, data_13_1323.2]

/-- Complete interval computation for depth 13, residue 1324. -/
theorem bounds_13_1324 : exactInterval 13 1324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1324 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1324) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1324 : oddCount 1324 13 = 5 ∧ acceleratedOrbit 13 1324 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1324 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1324) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1324.1, data_13_1324.2]

/-- Complete interval computation for depth 13, residue 1325. -/
theorem bounds_13_1325 : exactInterval 13 1325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1325 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1325) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1325 : oddCount 1325 13 = 5 ∧ acceleratedOrbit 13 1325 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1325 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1325) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1325.1, data_13_1325.2]

end Collatz.Research.StoppingAtlas.Batch0553
