import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0169

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1556. -/
theorem bounds_11_1556 : exactInterval 11 1556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1556 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1556) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1556 : oddCount 1556 11 = 5 ∧ acceleratedOrbit 11 1556 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1556 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1556) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1556.1, data_11_1556.2]

/-- Complete interval computation for depth 11, residue 1557. -/
theorem bounds_11_1557 : exactInterval 11 1557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1557 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1557) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1557 : oddCount 1557 11 = 5 ∧ acceleratedOrbit 11 1557 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1557 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1557) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1557.1, data_11_1557.2]

/-- Complete interval computation for depth 11, residue 1558. -/
theorem bounds_11_1558 : exactInterval 11 1558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1558 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1558) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1558 : oddCount 1558 11 = 6 ∧ acceleratedOrbit 11 1558 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1558 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1558) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1558.1, data_11_1558.2]

/-- Complete interval computation for depth 11, residue 1559. -/
theorem bounds_11_1559 : exactInterval 11 1559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1559 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1559) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1559 : oddCount 1559 11 = 6 ∧ acceleratedOrbit 11 1559 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1559 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1559) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1559.1, data_11_1559.2]

/-- Complete interval computation for depth 11, residue 1560. -/
theorem bounds_11_1560 : exactInterval 11 1560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1560 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1560) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1560 : oddCount 1560 11 = 5 ∧ acceleratedOrbit 11 1560 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1560 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1560) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1560.1, data_11_1560.2]

/-- Complete interval computation for depth 11, residue 1561. -/
theorem bounds_11_1561 : exactInterval 11 1561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1561 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1561) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1561 : oddCount 1561 11 = 6 ∧ acceleratedOrbit 11 1561 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1561 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1561) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1561.1, data_11_1561.2]

/-- Complete interval computation for depth 11, residue 1562. -/
theorem bounds_11_1562 : exactInterval 11 1562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1562 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1562) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1562 : oddCount 1562 11 = 5 ∧ acceleratedOrbit 11 1562 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1562 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1562) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1562.1, data_11_1562.2]

/-- Complete interval computation for depth 11, residue 1563. -/
theorem bounds_11_1563 : exactInterval 11 1563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1563 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1563) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1563 : oddCount 1563 11 = 8 ∧ acceleratedOrbit 11 1563 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1563 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1563) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1563.1, data_11_1563.2]

/-- Complete interval computation for depth 11, residue 1564. -/
theorem bounds_11_1564 : exactInterval 11 1564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1564 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1564) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1564 : oddCount 1564 11 = 4 ∧ acceleratedOrbit 11 1564 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1564 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1564) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1564.1, data_11_1564.2]

/-- Complete interval computation for depth 11, residue 1565. -/
theorem bounds_11_1565 : exactInterval 11 1565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1565 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1565) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1565 : oddCount 1565 11 = 4 ∧ acceleratedOrbit 11 1565 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1565 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1565) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1565.1, data_11_1565.2]

/-- Complete interval computation for depth 11, residue 1566. -/
theorem bounds_11_1566 : exactInterval 11 1566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1566 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1566) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1566 : oddCount 1566 11 = 4 ∧ acceleratedOrbit 11 1566 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1566 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1566) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1566.1, data_11_1566.2]

/-- Complete interval computation for depth 11, residue 1567. -/
theorem bounds_11_1567 : exactInterval 11 1567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1567 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1567) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1567 : oddCount 1567 11 = 8 ∧ acceleratedOrbit 11 1567 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1567 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1567) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1567.1, data_11_1567.2]

/-- Complete interval computation for depth 11, residue 1568. -/
theorem bounds_11_1568 : exactInterval 11 1568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1568 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1568) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1568 : oddCount 1568 11 = 2 ∧ acceleratedOrbit 11 1568 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1568 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1568) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1568.1, data_11_1568.2]

/-- Complete interval computation for depth 11, residue 1569. -/
theorem bounds_11_1569 : exactInterval 11 1569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1569 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1569) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1569 : oddCount 1569 11 = 6 ∧ acceleratedOrbit 11 1569 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1569 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1569) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1569.1, data_11_1569.2]

/-- Complete interval computation for depth 11, residue 1570. -/
theorem bounds_11_1570 : exactInterval 11 1570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1570 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1570) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1570 : oddCount 1570 11 = 5 ∧ acceleratedOrbit 11 1570 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1570 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1570) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1570.1, data_11_1570.2]

end Collatz.Research.StoppingAtlas.Batch0169
