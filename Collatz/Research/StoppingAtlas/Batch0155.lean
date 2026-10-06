import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0155

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1341. -/
theorem bounds_11_1341 : exactInterval 11 1341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1341 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1341) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1341 : oddCount 1341 11 = 6 ∧ acceleratedOrbit 11 1341 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1341 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1341) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1341.1, data_11_1341.2]

/-- Complete interval computation for depth 11, residue 1342. -/
theorem bounds_11_1342 : exactInterval 11 1342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1342 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1342) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1342 : oddCount 1342 11 = 8 ∧ acceleratedOrbit 11 1342 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1342 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1342) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1342.1, data_11_1342.2]

/-- Complete interval computation for depth 11, residue 1343. -/
theorem bounds_11_1343 : exactInterval 11 1343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1343 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1343) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1343 : oddCount 1343 11 = 8 ∧ acceleratedOrbit 11 1343 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1343 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1343) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1343.1, data_11_1343.2]

/-- Complete interval computation for depth 11, residue 1344. -/
theorem bounds_11_1344 : exactInterval 11 1344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1344 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1344) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1344 : oddCount 1344 11 = 1 ∧ acceleratedOrbit 11 1344 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1344 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1344) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1344.1, data_11_1344.2]

/-- Complete interval computation for depth 11, residue 1345. -/
theorem bounds_11_1345 : exactInterval 11 1345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1345 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1345) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1345 : oddCount 1345 11 = 5 ∧ acceleratedOrbit 11 1345 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1345 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1345) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1345.1, data_11_1345.2]

/-- Complete interval computation for depth 11, residue 1346. -/
theorem bounds_11_1346 : exactInterval 11 1346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1346 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1346) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1346 : oddCount 1346 11 = 6 ∧ acceleratedOrbit 11 1346 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1346 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1346) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1346.1, data_11_1346.2]

/-- Complete interval computation for depth 11, residue 1347. -/
theorem bounds_11_1347 : exactInterval 11 1347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1347 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1347) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1347 : oddCount 1347 11 = 6 ∧ acceleratedOrbit 11 1347 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1347 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1347) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1347.1, data_11_1347.2]

/-- Complete interval computation for depth 11, residue 1348. -/
theorem bounds_11_1348 : exactInterval 11 1348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1348 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1348) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1348 : oddCount 1348 11 = 6 ∧ acceleratedOrbit 11 1348 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1348 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1348) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1348.1, data_11_1348.2]

/-- Complete interval computation for depth 11, residue 1349. -/
theorem bounds_11_1349 : exactInterval 11 1349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1349 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1349) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1349 : oddCount 1349 11 = 6 ∧ acceleratedOrbit 11 1349 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1349 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1349) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1349.1, data_11_1349.2]

/-- Complete interval computation for depth 11, residue 1350. -/
theorem bounds_11_1350 : exactInterval 11 1350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1350 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1350) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1350 : oddCount 1350 11 = 6 ∧ acceleratedOrbit 11 1350 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1350 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1350) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1350.1, data_11_1350.2]

/-- Complete interval computation for depth 11, residue 1351. -/
theorem bounds_11_1351 : exactInterval 11 1351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1351 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1351) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1351 : oddCount 1351 11 = 8 ∧ acceleratedOrbit 11 1351 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1351 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1351) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1351.1, data_11_1351.2]

/-- Complete interval computation for depth 11, residue 1352. -/
theorem bounds_11_1352 : exactInterval 11 1352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1352 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1352) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1352 : oddCount 1352 11 = 7 ∧ acceleratedOrbit 11 1352 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1352 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1352) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1352.1, data_11_1352.2]

/-- Complete interval computation for depth 11, residue 1353. -/
theorem bounds_11_1353 : exactInterval 11 1353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1353 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1353) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1353 : oddCount 1353 11 = 7 ∧ acceleratedOrbit 11 1353 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1353 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1353) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1353.1, data_11_1353.2]

/-- Complete interval computation for depth 11, residue 1354. -/
theorem bounds_11_1354 : exactInterval 11 1354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1354 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1354) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1354 : oddCount 1354 11 = 7 ∧ acceleratedOrbit 11 1354 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1354 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1354) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1354.1, data_11_1354.2]

/-- Complete interval computation for depth 11, residue 1355. -/
theorem bounds_11_1355 : exactInterval 11 1355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1355 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1355) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1355 : oddCount 1355 11 = 6 ∧ acceleratedOrbit 11 1355 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1355 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1355) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1355.1, data_11_1355.2]

end Collatz.Research.StoppingAtlas.Batch0155
