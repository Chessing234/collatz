import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0294

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1428. -/
theorem bounds_12_1428 : exactInterval 12 1428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1428 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1428) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1428 : oddCount 1428 12 = 4 ∧ acceleratedOrbit 12 1428 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1428 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1428) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1428.1, data_12_1428.2]

/-- Complete interval computation for depth 12, residue 1429. -/
theorem bounds_12_1429 : exactInterval 12 1429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1429 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1429) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1429 : oddCount 1429 12 = 4 ∧ acceleratedOrbit 12 1429 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1429 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1429) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1429.1, data_12_1429.2]

/-- Complete interval computation for depth 12, residue 1430. -/
theorem bounds_12_1430 : exactInterval 12 1430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1430 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1430) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1430 : oddCount 1430 12 = 6 ∧ acceleratedOrbit 12 1430 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1430 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1430) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1430.1, data_12_1430.2]

/-- Complete interval computation for depth 12, residue 1431. -/
theorem bounds_12_1431 : exactInterval 12 1431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1431 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1431) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1431 : oddCount 1431 12 = 6 ∧ acceleratedOrbit 12 1431 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1431 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1431) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1431.1, data_12_1431.2]

/-- Complete interval computation for depth 12, residue 1432. -/
theorem bounds_12_1432 : exactInterval 12 1432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1432 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1432) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1432 : oddCount 1432 12 = 4 ∧ acceleratedOrbit 12 1432 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1432 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1432) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1432.1, data_12_1432.2]

/-- Complete interval computation for depth 12, residue 1433. -/
theorem bounds_12_1433 : exactInterval 12 1433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1433 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1433) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1433 : oddCount 1433 12 = 6 ∧ acceleratedOrbit 12 1433 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1433 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1433) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1433.1, data_12_1433.2]

/-- Complete interval computation for depth 12, residue 1434. -/
theorem bounds_12_1434 : exactInterval 12 1434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1434 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1434) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1434 : oddCount 1434 12 = 4 ∧ acceleratedOrbit 12 1434 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1434 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1434) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1434.1, data_12_1434.2]

/-- Complete interval computation for depth 12, residue 1435. -/
theorem bounds_12_1435 : exactInterval 12 1435 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1435 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1435) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1435 : oddCount 1435 12 = 7 ∧ acceleratedOrbit 12 1435 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1435 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1435) = 3 ^ 7 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1435.1, data_12_1435.2]

/-- Complete interval computation for depth 12, residue 1436. -/
theorem bounds_12_1436 : exactInterval 12 1436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1436 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1436) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1436 : oddCount 1436 12 = 8 ∧ acceleratedOrbit 12 1436 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1436 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1436) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1436.1, data_12_1436.2]

/-- Complete interval computation for depth 12, residue 1437. -/
theorem bounds_12_1437 : exactInterval 12 1437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1437 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1437) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1437 : oddCount 1437 12 = 8 ∧ acceleratedOrbit 12 1437 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1437 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1437) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1437.1, data_12_1437.2]

/-- Complete interval computation for depth 12, residue 1438. -/
theorem bounds_12_1438 : exactInterval 12 1438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1438 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1438) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1438 : oddCount 1438 12 = 8 ∧ acceleratedOrbit 12 1438 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1438 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1438) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1438.1, data_12_1438.2]

/-- Complete interval computation for depth 12, residue 1439. -/
theorem bounds_12_1439 : exactInterval 12 1439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1439 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1439) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1439 : oddCount 1439 12 = 10 ∧ acceleratedOrbit 12 1439 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1439 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1439) = 3 ^ 10 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1439.1, data_12_1439.2]

/-- Complete interval computation for depth 12, residue 1440. -/
theorem bounds_12_1440 : exactInterval 12 1440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1440 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1440) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1440 : oddCount 1440 12 = 3 ∧ acceleratedOrbit 12 1440 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1440 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1440) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1440.1, data_12_1440.2]

/-- Complete interval computation for depth 12, residue 1441. -/
theorem bounds_12_1441 : exactInterval 12 1441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1441 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1441) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1441 : oddCount 1441 12 = 6 ∧ acceleratedOrbit 12 1441 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1441 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1441) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1441.1, data_12_1441.2]

/-- Complete interval computation for depth 12, residue 1442. -/
theorem bounds_12_1442 : exactInterval 12 1442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1442 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1442) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1442 : oddCount 1442 12 = 5 ∧ acceleratedOrbit 12 1442 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1442 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1442) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1442.1, data_12_1442.2]

end Collatz.Research.StoppingAtlas.Batch0294
