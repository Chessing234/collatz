import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0302

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1551. -/
theorem bounds_12_1551 : exactInterval 12 1551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1551 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1551) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1551 : oddCount 1551 12 = 7 ∧ acceleratedOrbit 12 1551 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1551 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1551) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1551.1, data_12_1551.2]

/-- Complete interval computation for depth 12, residue 1552. -/
theorem bounds_12_1552 : exactInterval 12 1552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1552 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1552) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1552 : oddCount 1552 12 = 5 ∧ acceleratedOrbit 12 1552 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1552 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1552) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1552.1, data_12_1552.2]

/-- Complete interval computation for depth 12, residue 1553. -/
theorem bounds_12_1553 : exactInterval 12 1553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1553 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1553) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1553 : oddCount 1553 12 = 4 ∧ acceleratedOrbit 12 1553 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1553 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1553) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1553.1, data_12_1553.2]

/-- Complete interval computation for depth 12, residue 1554. -/
theorem bounds_12_1554 : exactInterval 12 1554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1554 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1554) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1554 : oddCount 1554 12 = 7 ∧ acceleratedOrbit 12 1554 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1554 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1554) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1554.1, data_12_1554.2]

/-- Complete interval computation for depth 12, residue 1555. -/
theorem bounds_12_1555 : exactInterval 12 1555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1555 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1555) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1555 : oddCount 1555 12 = 7 ∧ acceleratedOrbit 12 1555 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1555 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1555) = 3 ^ 7 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1555.1, data_12_1555.2]

/-- Complete interval computation for depth 12, residue 1556. -/
theorem bounds_12_1556 : exactInterval 12 1556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1556 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1556) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1556 : oddCount 1556 12 = 5 ∧ acceleratedOrbit 12 1556 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1556 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1556) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1556.1, data_12_1556.2]

/-- Complete interval computation for depth 12, residue 1557. -/
theorem bounds_12_1557 : exactInterval 12 1557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1557 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1557) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1557 : oddCount 1557 12 = 5 ∧ acceleratedOrbit 12 1557 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1557 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1557) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1557.1, data_12_1557.2]

/-- Complete interval computation for depth 12, residue 1558. -/
theorem bounds_12_1558 : exactInterval 12 1558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1558 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1558) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1558 : oddCount 1558 12 = 7 ∧ acceleratedOrbit 12 1558 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1558 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1558) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1558.1, data_12_1558.2]

/-- Complete interval computation for depth 12, residue 1559. -/
theorem bounds_12_1559 : exactInterval 12 1559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1559 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1559) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1559 : oddCount 1559 12 = 7 ∧ acceleratedOrbit 12 1559 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1559 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1559) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1559.1, data_12_1559.2]

/-- Complete interval computation for depth 12, residue 1560. -/
theorem bounds_12_1560 : exactInterval 12 1560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1560 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1560) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1560 : oddCount 1560 12 = 5 ∧ acceleratedOrbit 12 1560 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1560 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1560) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1560.1, data_12_1560.2]

/-- Complete interval computation for depth 12, residue 1561. -/
theorem bounds_12_1561 : exactInterval 12 1561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1561 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1561) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1561 : oddCount 1561 12 = 7 ∧ acceleratedOrbit 12 1561 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1561 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1561) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1561.1, data_12_1561.2]

/-- Complete interval computation for depth 12, residue 1562. -/
theorem bounds_12_1562 : exactInterval 12 1562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1562 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1562) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1562 : oddCount 1562 12 = 5 ∧ acceleratedOrbit 12 1562 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1562 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1562) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1562.1, data_12_1562.2]

/-- Complete interval computation for depth 12, residue 1563. -/
theorem bounds_12_1563 : exactInterval 12 1563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1563 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1563) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1563 : oddCount 1563 12 = 8 ∧ acceleratedOrbit 12 1563 = 2506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1563 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1563) = 3 ^ 8 * m + 2506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1563.1, data_12_1563.2]

/-- Complete interval computation for depth 12, residue 1564. -/
theorem bounds_12_1564 : exactInterval 12 1564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1564 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1564) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1564 : oddCount 1564 12 = 4 ∧ acceleratedOrbit 12 1564 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1564 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1564) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1564.1, data_12_1564.2]

/-- Complete interval computation for depth 12, residue 1565. -/
theorem bounds_12_1565 : exactInterval 12 1565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1565 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1565) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1565 : oddCount 1565 12 = 4 ∧ acceleratedOrbit 12 1565 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1565 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1565) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1565.1, data_12_1565.2]

end Collatz.Research.StoppingAtlas.Batch0302
