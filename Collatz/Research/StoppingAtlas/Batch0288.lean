import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0288

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1336. -/
theorem bounds_12_1336 : exactInterval 12 1336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1336 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1336) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1336 : oddCount 1336 12 = 7 ∧ acceleratedOrbit 12 1336 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1336 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1336) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1336.1, data_12_1336.2]

/-- Complete interval computation for depth 12, residue 1337. -/
theorem bounds_12_1337 : exactInterval 12 1337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1337 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1337) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1337 : oddCount 1337 12 = 8 ∧ acceleratedOrbit 12 1337 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1337 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1337) = 3 ^ 8 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1337.1, data_12_1337.2]

/-- Complete interval computation for depth 12, residue 1338. -/
theorem bounds_12_1338 : exactInterval 12 1338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1338 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1338) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1338 : oddCount 1338 12 = 7 ∧ acceleratedOrbit 12 1338 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1338 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1338) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1338.1, data_12_1338.2]

/-- Complete interval computation for depth 12, residue 1339. -/
theorem bounds_12_1339 : exactInterval 12 1339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1339 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1339) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1339 : oddCount 1339 12 = 5 ∧ acceleratedOrbit 12 1339 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1339 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1339) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1339.1, data_12_1339.2]

/-- Complete interval computation for depth 12, residue 1340. -/
theorem bounds_12_1340 : exactInterval 12 1340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1340 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1340) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1340 : oddCount 1340 12 = 7 ∧ acceleratedOrbit 12 1340 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1340 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1340) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1340.1, data_12_1340.2]

/-- Complete interval computation for depth 12, residue 1341. -/
theorem bounds_12_1341 : exactInterval 12 1341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1341 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1341) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1341 : oddCount 1341 12 = 7 ∧ acceleratedOrbit 12 1341 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1341 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1341) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1341.1, data_12_1341.2]

/-- Complete interval computation for depth 12, residue 1342. -/
theorem bounds_12_1342 : exactInterval 12 1342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1342 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1342) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1342 : oddCount 1342 12 = 8 ∧ acceleratedOrbit 12 1342 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1342 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1342) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1342.1, data_12_1342.2]

/-- Complete interval computation for depth 12, residue 1343. -/
theorem bounds_12_1343 : exactInterval 12 1343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1343 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1343) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1343 : oddCount 1343 12 = 8 ∧ acceleratedOrbit 12 1343 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1343 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1343) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1343.1, data_12_1343.2]

/-- Complete interval computation for depth 12, residue 1344. -/
theorem bounds_12_1344 : exactInterval 12 1344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1344 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1344) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1344 : oddCount 1344 12 = 1 ∧ acceleratedOrbit 12 1344 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1344 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1344) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1344.1, data_12_1344.2]

/-- Complete interval computation for depth 12, residue 1345. -/
theorem bounds_12_1345 : exactInterval 12 1345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1345 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1345) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1345 : oddCount 1345 12 = 6 ∧ acceleratedOrbit 12 1345 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1345 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1345) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1345.1, data_12_1345.2]

/-- Complete interval computation for depth 12, residue 1346. -/
theorem bounds_12_1346 : exactInterval 12 1346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1346 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1346) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1346 : oddCount 1346 12 = 7 ∧ acceleratedOrbit 12 1346 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1346 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1346) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1346.1, data_12_1346.2]

/-- Complete interval computation for depth 12, residue 1347. -/
theorem bounds_12_1347 : exactInterval 12 1347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1347 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1347) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1347 : oddCount 1347 12 = 7 ∧ acceleratedOrbit 12 1347 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1347 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1347) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1347.1, data_12_1347.2]

/-- Complete interval computation for depth 12, residue 1348. -/
theorem bounds_12_1348 : exactInterval 12 1348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1348 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1348) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1348 : oddCount 1348 12 = 7 ∧ acceleratedOrbit 12 1348 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1348 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1348) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1348.1, data_12_1348.2]

/-- Complete interval computation for depth 12, residue 1349. -/
theorem bounds_12_1349 : exactInterval 12 1349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1349 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1349) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1349 : oddCount 1349 12 = 7 ∧ acceleratedOrbit 12 1349 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1349 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1349) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1349.1, data_12_1349.2]

/-- Complete interval computation for depth 12, residue 1350. -/
theorem bounds_12_1350 : exactInterval 12 1350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1350 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1350) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1350 : oddCount 1350 12 = 7 ∧ acceleratedOrbit 12 1350 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1350 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1350) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1350.1, data_12_1350.2]

end Collatz.Research.StoppingAtlas.Batch0288
