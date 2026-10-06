import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0570

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1571. -/
theorem bounds_13_1571 : exactInterval 13 1571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1571 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1571) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1571 : oddCount 1571 13 = 5 ∧ acceleratedOrbit 13 1571 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1571 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1571) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1571.1, data_13_1571.2]

/-- Complete interval computation for depth 13, residue 1572. -/
theorem bounds_13_1572 : exactInterval 13 1572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1572 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1572) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1572 : oddCount 1572 13 = 7 ∧ acceleratedOrbit 13 1572 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1572 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1572) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1572.1, data_13_1572.2]

/-- Complete interval computation for depth 13, residue 1573. -/
theorem bounds_13_1573 : exactInterval 13 1573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1573 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1573) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1573 : oddCount 1573 13 = 7 ∧ acceleratedOrbit 13 1573 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1573 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1573) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1573.1, data_13_1573.2]

/-- Complete interval computation for depth 13, residue 1574. -/
theorem bounds_13_1574 : exactInterval 13 1574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1574 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1574) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1574 : oddCount 1574 13 = 7 ∧ acceleratedOrbit 13 1574 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1574 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1574) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1574.1, data_13_1574.2]

/-- Complete interval computation for depth 13, residue 1575. -/
theorem bounds_13_1575 : exactInterval 13 1575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1575 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1575) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1575 : oddCount 1575 13 = 7 ∧ acceleratedOrbit 13 1575 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1575 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1575) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1575.1, data_13_1575.2]

/-- Complete interval computation for depth 13, residue 1576. -/
theorem bounds_13_1576 : exactInterval 13 1576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1576 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1576) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1576 : oddCount 1576 13 = 4 ∧ acceleratedOrbit 13 1576 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1576 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1576) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1576.1, data_13_1576.2]

/-- Complete interval computation for depth 13, residue 1577. -/
theorem bounds_13_1577 : exactInterval 13 1577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1577 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1577) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1577 : oddCount 1577 13 = 10 ∧ acceleratedOrbit 13 1577 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1577 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1577) = 3 ^ 10 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1577.1, data_13_1577.2]

/-- Complete interval computation for depth 13, residue 1578. -/
theorem bounds_13_1578 : exactInterval 13 1578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1578 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1578) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1578 : oddCount 1578 13 = 4 ∧ acceleratedOrbit 13 1578 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1578 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1578) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1578.1, data_13_1578.2]

/-- Complete interval computation for depth 13, residue 1579. -/
theorem bounds_13_1579 : exactInterval 13 1579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1579 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1579) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1579 : oddCount 1579 13 = 5 ∧ acceleratedOrbit 13 1579 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1579 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1579) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1579.1, data_13_1579.2]

/-- Complete interval computation for depth 13, residue 1580. -/
theorem bounds_13_1580 : exactInterval 13 1580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1580 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1580) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1580 : oddCount 1580 13 = 7 ∧ acceleratedOrbit 13 1580 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1580 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1580) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1580.1, data_13_1580.2]

/-- Complete interval computation for depth 13, residue 1581. -/
theorem bounds_13_1581 : exactInterval 13 1581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1581 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1581) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1581 : oddCount 1581 13 = 7 ∧ acceleratedOrbit 13 1581 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1581 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1581) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1581.1, data_13_1581.2]

/-- Complete interval computation for depth 13, residue 1582. -/
theorem bounds_13_1582 : exactInterval 13 1582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1582 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1582) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1582 : oddCount 1582 13 = 7 ∧ acceleratedOrbit 13 1582 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1582 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1582) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1582.1, data_13_1582.2]

/-- Complete interval computation for depth 13, residue 1583. -/
theorem bounds_13_1583 : exactInterval 13 1583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1583 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1583) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1583 : oddCount 1583 13 = 11 ∧ acceleratedOrbit 13 1583 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1583 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1583) = 3 ^ 11 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1583.1, data_13_1583.2]

/-- Complete interval computation for depth 13, residue 1584. -/
theorem bounds_13_1584 : exactInterval 13 1584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1584 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1584) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1584 : oddCount 1584 13 = 4 ∧ acceleratedOrbit 13 1584 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1584 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1584) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1584.1, data_13_1584.2]

/-- Complete interval computation for depth 13, residue 1585. -/
theorem bounds_13_1585 : exactInterval 13 1585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1585 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1585) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1585 : oddCount 1585 13 = 7 ∧ acceleratedOrbit 13 1585 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1585 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1585) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1585.1, data_13_1585.2]

/-- Complete interval computation for depth 13, residue 1586. -/
theorem bounds_13_1586 : exactInterval 13 1586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1586 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1586) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1586 : oddCount 1586 13 = 7 ∧ acceleratedOrbit 13 1586 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1586 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1586) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1586.1, data_13_1586.2]

end Collatz.Research.StoppingAtlas.Batch0570
