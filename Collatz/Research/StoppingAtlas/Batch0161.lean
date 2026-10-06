import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0161

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1433. -/
theorem bounds_11_1433 : exactInterval 11 1433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1433 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1433) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1433 : oddCount 1433 11 = 6 ∧ acceleratedOrbit 11 1433 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1433 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1433) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1433.1, data_11_1433.2]

/-- Complete interval computation for depth 11, residue 1434. -/
theorem bounds_11_1434 : exactInterval 11 1434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1434 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1434) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1434 : oddCount 1434 11 = 3 ∧ acceleratedOrbit 11 1434 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1434 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1434) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1434.1, data_11_1434.2]

/-- Complete interval computation for depth 11, residue 1435. -/
theorem bounds_11_1435 : exactInterval 11 1435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1435 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1435) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1435 : oddCount 1435 11 = 7 ∧ acceleratedOrbit 11 1435 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1435 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1435) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1435.1, data_11_1435.2]

/-- Complete interval computation for depth 11, residue 1436. -/
theorem bounds_11_1436 : exactInterval 11 1436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1436 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1436) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1436 : oddCount 1436 11 = 8 ∧ acceleratedOrbit 11 1436 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1436 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1436) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1436.1, data_11_1436.2]

/-- Complete interval computation for depth 11, residue 1437. -/
theorem bounds_11_1437 : exactInterval 11 1437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1437 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1437) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1437 : oddCount 1437 11 = 8 ∧ acceleratedOrbit 11 1437 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1437 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1437) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1437.1, data_11_1437.2]

/-- Complete interval computation for depth 11, residue 1438. -/
theorem bounds_11_1438 : exactInterval 11 1438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1438 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1438) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1438 : oddCount 1438 11 = 8 ∧ acceleratedOrbit 11 1438 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1438 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1438) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1438.1, data_11_1438.2]

/-- Complete interval computation for depth 11, residue 1439. -/
theorem bounds_11_1439 : exactInterval 11 1439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1439 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1439) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1439 : oddCount 1439 11 = 9 ∧ acceleratedOrbit 11 1439 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1439 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1439) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1439.1, data_11_1439.2]

/-- Complete interval computation for depth 11, residue 1440. -/
theorem bounds_11_1440 : exactInterval 11 1440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1440 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1440) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1440 : oddCount 1440 11 = 3 ∧ acceleratedOrbit 11 1440 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1440 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1440) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1440.1, data_11_1440.2]

/-- Complete interval computation for depth 11, residue 1441. -/
theorem bounds_11_1441 : exactInterval 11 1441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1441 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1441) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1441 : oddCount 1441 11 = 6 ∧ acceleratedOrbit 11 1441 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1441 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1441) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1441.1, data_11_1441.2]

/-- Complete interval computation for depth 11, residue 1442. -/
theorem bounds_11_1442 : exactInterval 11 1442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1442 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1442) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1442 : oddCount 1442 11 = 5 ∧ acceleratedOrbit 11 1442 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1442 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1442) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1442.1, data_11_1442.2]

/-- Complete interval computation for depth 11, residue 1443. -/
theorem bounds_11_1443 : exactInterval 11 1443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1443 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1443) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1443 : oddCount 1443 11 = 5 ∧ acceleratedOrbit 11 1443 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1443 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1443) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1443.1, data_11_1443.2]

/-- Complete interval computation for depth 11, residue 1444. -/
theorem bounds_11_1444 : exactInterval 11 1444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1444 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1444) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1444 : oddCount 1444 11 = 5 ∧ acceleratedOrbit 11 1444 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1444 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1444) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1444.1, data_11_1444.2]

/-- Complete interval computation for depth 11, residue 1445. -/
theorem bounds_11_1445 : exactInterval 11 1445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1445 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1445) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1445 : oddCount 1445 11 = 5 ∧ acceleratedOrbit 11 1445 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1445 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1445) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1445.1, data_11_1445.2]

/-- Complete interval computation for depth 11, residue 1446. -/
theorem bounds_11_1446 : exactInterval 11 1446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1446 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1446) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1446 : oddCount 1446 11 = 5 ∧ acceleratedOrbit 11 1446 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1446 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1446) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1446.1, data_11_1446.2]

/-- Complete interval computation for depth 11, residue 1447. -/
theorem bounds_11_1447 : exactInterval 11 1447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1447 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1447) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1447 : oddCount 1447 11 = 7 ∧ acceleratedOrbit 11 1447 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1447 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1447) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1447.1, data_11_1447.2]

end Collatz.Research.StoppingAtlas.Batch0161
