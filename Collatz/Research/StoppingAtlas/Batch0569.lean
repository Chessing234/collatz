import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0569

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1556. -/
theorem bounds_13_1556 : exactInterval 13 1556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1556 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1556) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1556 : oddCount 1556 13 = 5 ∧ acceleratedOrbit 13 1556 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1556 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1556) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1556.1, data_13_1556.2]

/-- Complete interval computation for depth 13, residue 1557. -/
theorem bounds_13_1557 : exactInterval 13 1557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1557 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1557) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1557 : oddCount 1557 13 = 5 ∧ acceleratedOrbit 13 1557 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1557 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1557) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1557.1, data_13_1557.2]

/-- Complete interval computation for depth 13, residue 1558. -/
theorem bounds_13_1558 : exactInterval 13 1558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1558 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1558) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1558 : oddCount 1558 13 = 7 ∧ acceleratedOrbit 13 1558 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1558 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1558) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1558.1, data_13_1558.2]

/-- Complete interval computation for depth 13, residue 1559. -/
theorem bounds_13_1559 : exactInterval 13 1559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1559 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1559) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1559 : oddCount 1559 13 = 7 ∧ acceleratedOrbit 13 1559 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1559 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1559) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1559.1, data_13_1559.2]

/-- Complete interval computation for depth 13, residue 1560. -/
theorem bounds_13_1560 : exactInterval 13 1560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1560 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1560) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1560 : oddCount 1560 13 = 5 ∧ acceleratedOrbit 13 1560 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1560 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1560) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1560.1, data_13_1560.2]

/-- Complete interval computation for depth 13, residue 1561. -/
theorem bounds_13_1561 : exactInterval 13 1561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1561 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1561) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1561 : oddCount 1561 13 = 7 ∧ acceleratedOrbit 13 1561 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1561 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1561) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1561.1, data_13_1561.2]

/-- Complete interval computation for depth 13, residue 1562. -/
theorem bounds_13_1562 : exactInterval 13 1562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1562 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1562) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1562 : oddCount 1562 13 = 5 ∧ acceleratedOrbit 13 1562 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1562 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1562) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1562.1, data_13_1562.2]

/-- Complete interval computation for depth 13, residue 1563. -/
theorem bounds_13_1563 : exactInterval 13 1563 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1563 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1563) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1563 : oddCount 1563 13 = 8 ∧ acceleratedOrbit 13 1563 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1563 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1563) = 3 ^ 8 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1563.1, data_13_1563.2]

/-- Complete interval computation for depth 13, residue 1564. -/
theorem bounds_13_1564 : exactInterval 13 1564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1564 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1564) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1564 : oddCount 1564 13 = 5 ∧ acceleratedOrbit 13 1564 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1564 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1564) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1564.1, data_13_1564.2]

/-- Complete interval computation for depth 13, residue 1565. -/
theorem bounds_13_1565 : exactInterval 13 1565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1565 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1565) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1565 : oddCount 1565 13 = 5 ∧ acceleratedOrbit 13 1565 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1565 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1565) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1565.1, data_13_1565.2]

/-- Complete interval computation for depth 13, residue 1566. -/
theorem bounds_13_1566 : exactInterval 13 1566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1566 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1566) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1566 : oddCount 1566 13 = 5 ∧ acceleratedOrbit 13 1566 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1566 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1566) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1566.1, data_13_1566.2]

/-- Complete interval computation for depth 13, residue 1567. -/
theorem bounds_13_1567 : exactInterval 13 1567 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1567 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1567) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1567 : oddCount 1567 13 = 8 ∧ acceleratedOrbit 13 1567 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1567 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1567) = 3 ^ 8 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1567.1, data_13_1567.2]

/-- Complete interval computation for depth 13, residue 1568. -/
theorem bounds_13_1568 : exactInterval 13 1568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1568 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1568) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1568 : oddCount 1568 13 = 4 ∧ acceleratedOrbit 13 1568 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1568 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1568) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1568.1, data_13_1568.2]

/-- Complete interval computation for depth 13, residue 1569. -/
theorem bounds_13_1569 : exactInterval 13 1569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1569 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1569) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1569 : oddCount 1569 13 = 6 ∧ acceleratedOrbit 13 1569 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1569 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1569) = 3 ^ 6 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1569.1, data_13_1569.2]

/-- Complete interval computation for depth 13, residue 1570. -/
theorem bounds_13_1570 : exactInterval 13 1570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1570 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1570) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1570 : oddCount 1570 13 = 5 ∧ acceleratedOrbit 13 1570 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1570 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1570) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1570.1, data_13_1570.2]

end Collatz.Research.StoppingAtlas.Batch0569
