import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0555

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1341. -/
theorem bounds_13_1341 : exactInterval 13 1341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1341 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1341) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1341 : oddCount 1341 13 = 8 ∧ acceleratedOrbit 13 1341 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1341 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1341) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1341.1, data_13_1341.2]

/-- Complete interval computation for depth 13, residue 1342. -/
theorem bounds_13_1342 : exactInterval 13 1342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1342 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1342) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1342 : oddCount 1342 13 = 9 ∧ acceleratedOrbit 13 1342 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1342 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1342) = 3 ^ 9 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1342.1, data_13_1342.2]

/-- Complete interval computation for depth 13, residue 1343. -/
theorem bounds_13_1343 : exactInterval 13 1343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1343 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1343) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1343 : oddCount 1343 13 = 9 ∧ acceleratedOrbit 13 1343 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1343 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1343) = 3 ^ 9 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1343.1, data_13_1343.2]

/-- Complete interval computation for depth 13, residue 1344. -/
theorem bounds_13_1344 : exactInterval 13 1344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1344 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1344) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1344 : oddCount 1344 13 = 2 ∧ acceleratedOrbit 13 1344 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1344 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1344) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1344.1, data_13_1344.2]

/-- Complete interval computation for depth 13, residue 1345. -/
theorem bounds_13_1345 : exactInterval 13 1345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1345 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1345) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1345 : oddCount 1345 13 = 6 ∧ acceleratedOrbit 13 1345 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1345 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1345) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1345.1, data_13_1345.2]

/-- Complete interval computation for depth 13, residue 1346. -/
theorem bounds_13_1346 : exactInterval 13 1346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1346 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1346) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1346 : oddCount 1346 13 = 7 ∧ acceleratedOrbit 13 1346 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1346 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1346) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1346.1, data_13_1346.2]

/-- Complete interval computation for depth 13, residue 1347. -/
theorem bounds_13_1347 : exactInterval 13 1347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1347 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1347) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1347 : oddCount 1347 13 = 7 ∧ acceleratedOrbit 13 1347 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1347 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1347) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1347.1, data_13_1347.2]

/-- Complete interval computation for depth 13, residue 1348. -/
theorem bounds_13_1348 : exactInterval 13 1348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1348 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1348) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1348 : oddCount 1348 13 = 7 ∧ acceleratedOrbit 13 1348 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1348 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1348) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1348.1, data_13_1348.2]

/-- Complete interval computation for depth 13, residue 1349. -/
theorem bounds_13_1349 : exactInterval 13 1349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1349 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1349) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1349 : oddCount 1349 13 = 7 ∧ acceleratedOrbit 13 1349 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1349 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1349) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1349.1, data_13_1349.2]

/-- Complete interval computation for depth 13, residue 1350. -/
theorem bounds_13_1350 : exactInterval 13 1350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1350 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1350) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1350 : oddCount 1350 13 = 7 ∧ acceleratedOrbit 13 1350 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1350 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1350) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1350.1, data_13_1350.2]

/-- Complete interval computation for depth 13, residue 1351. -/
theorem bounds_13_1351 : exactInterval 13 1351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1351 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1351) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1351 : oddCount 1351 13 = 9 ∧ acceleratedOrbit 13 1351 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1351 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1351) = 3 ^ 9 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1351.1, data_13_1351.2]

/-- Complete interval computation for depth 13, residue 1352. -/
theorem bounds_13_1352 : exactInterval 13 1352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1352 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1352) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1352 : oddCount 1352 13 = 8 ∧ acceleratedOrbit 13 1352 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1352 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1352) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1352.1, data_13_1352.2]

/-- Complete interval computation for depth 13, residue 1353. -/
theorem bounds_13_1353 : exactInterval 13 1353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1353 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1353) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1353 : oddCount 1353 13 = 7 ∧ acceleratedOrbit 13 1353 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1353 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1353) = 3 ^ 7 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1353.1, data_13_1353.2]

/-- Complete interval computation for depth 13, residue 1354. -/
theorem bounds_13_1354 : exactInterval 13 1354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1354 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1354) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1354 : oddCount 1354 13 = 8 ∧ acceleratedOrbit 13 1354 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1354 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1354) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1354.1, data_13_1354.2]

/-- Complete interval computation for depth 13, residue 1355. -/
theorem bounds_13_1355 : exactInterval 13 1355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1355 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1355) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1355 : oddCount 1355 13 = 7 ∧ acceleratedOrbit 13 1355 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1355 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1355) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1355.1, data_13_1355.2]

end Collatz.Research.StoppingAtlas.Batch0555
