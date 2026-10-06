import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0561

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1433. -/
theorem bounds_13_1433 : exactInterval 13 1433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1433 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1433) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1433 : oddCount 1433 13 = 6 ∧ acceleratedOrbit 13 1433 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1433 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1433) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1433.1, data_13_1433.2]

/-- Complete interval computation for depth 13, residue 1434. -/
theorem bounds_13_1434 : exactInterval 13 1434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1434 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1434) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1434 : oddCount 1434 13 = 5 ∧ acceleratedOrbit 13 1434 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1434 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1434) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1434.1, data_13_1434.2]

/-- Complete interval computation for depth 13, residue 1435. -/
theorem bounds_13_1435 : exactInterval 13 1435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1435 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1435) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1435 : oddCount 1435 13 = 8 ∧ acceleratedOrbit 13 1435 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1435 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1435) = 3 ^ 8 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1435.1, data_13_1435.2]

/-- Complete interval computation for depth 13, residue 1436. -/
theorem bounds_13_1436 : exactInterval 13 1436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1436 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1436) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1436 : oddCount 1436 13 = 8 ∧ acceleratedOrbit 13 1436 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1436 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1436) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1436.1, data_13_1436.2]

/-- Complete interval computation for depth 13, residue 1437. -/
theorem bounds_13_1437 : exactInterval 13 1437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1437 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1437) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1437 : oddCount 1437 13 = 8 ∧ acceleratedOrbit 13 1437 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1437 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1437) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1437.1, data_13_1437.2]

/-- Complete interval computation for depth 13, residue 1438. -/
theorem bounds_13_1438 : exactInterval 13 1438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1438 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1438) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1438 : oddCount 1438 13 = 8 ∧ acceleratedOrbit 13 1438 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1438 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1438) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1438.1, data_13_1438.2]

/-- Complete interval computation for depth 13, residue 1439. -/
theorem bounds_13_1439 : exactInterval 13 1439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1439 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1439) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1439 : oddCount 1439 13 = 10 ∧ acceleratedOrbit 13 1439 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1439 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1439) = 3 ^ 10 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1439.1, data_13_1439.2]

/-- Complete interval computation for depth 13, residue 1440. -/
theorem bounds_13_1440 : exactInterval 13 1440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1440 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1440) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1440 : oddCount 1440 13 = 3 ∧ acceleratedOrbit 13 1440 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1440 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1440) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1440.1, data_13_1440.2]

/-- Complete interval computation for depth 13, residue 1441. -/
theorem bounds_13_1441 : exactInterval 13 1441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1441 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1441) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1441 : oddCount 1441 13 = 7 ∧ acceleratedOrbit 13 1441 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1441 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1441) = 3 ^ 7 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1441.1, data_13_1441.2]

/-- Complete interval computation for depth 13, residue 1442. -/
theorem bounds_13_1442 : exactInterval 13 1442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1442 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1442) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1442 : oddCount 1442 13 = 5 ∧ acceleratedOrbit 13 1442 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1442 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1442) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1442.1, data_13_1442.2]

/-- Complete interval computation for depth 13, residue 1443. -/
theorem bounds_13_1443 : exactInterval 13 1443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1443 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1443) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1443 : oddCount 1443 13 = 5 ∧ acceleratedOrbit 13 1443 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1443 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1443) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1443.1, data_13_1443.2]

/-- Complete interval computation for depth 13, residue 1444. -/
theorem bounds_13_1444 : exactInterval 13 1444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1444 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1444) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1444 : oddCount 1444 13 = 5 ∧ acceleratedOrbit 13 1444 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1444 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1444) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1444.1, data_13_1444.2]

/-- Complete interval computation for depth 13, residue 1445. -/
theorem bounds_13_1445 : exactInterval 13 1445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1445 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1445) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1445 : oddCount 1445 13 = 5 ∧ acceleratedOrbit 13 1445 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1445 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1445) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1445.1, data_13_1445.2]

/-- Complete interval computation for depth 13, residue 1446. -/
theorem bounds_13_1446 : exactInterval 13 1446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1446 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1446) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1446 : oddCount 1446 13 = 5 ∧ acceleratedOrbit 13 1446 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1446 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1446) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1446.1, data_13_1446.2]

/-- Complete interval computation for depth 13, residue 1447. -/
theorem bounds_13_1447 : exactInterval 13 1447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1447 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1447) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1447 : oddCount 1447 13 = 9 ∧ acceleratedOrbit 13 1447 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1447 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1447) = 3 ^ 9 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1447.1, data_13_1447.2]

end Collatz.Research.StoppingAtlas.Batch0561
