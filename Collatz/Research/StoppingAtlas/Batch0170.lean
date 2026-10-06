import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0170

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1571. -/
theorem bounds_11_1571 : exactInterval 11 1571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1571 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1571) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1571 : oddCount 1571 11 = 5 ∧ acceleratedOrbit 11 1571 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1571 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1571) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1571.1, data_11_1571.2]

/-- Complete interval computation for depth 11, residue 1572. -/
theorem bounds_11_1572 : exactInterval 11 1572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1572 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1572) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1572 : oddCount 1572 11 = 6 ∧ acceleratedOrbit 11 1572 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1572 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1572) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1572.1, data_11_1572.2]

/-- Complete interval computation for depth 11, residue 1573. -/
theorem bounds_11_1573 : exactInterval 11 1573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1573 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1573) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1573 : oddCount 1573 11 = 6 ∧ acceleratedOrbit 11 1573 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1573 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1573) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1573.1, data_11_1573.2]

/-- Complete interval computation for depth 11, residue 1574. -/
theorem bounds_11_1574 : exactInterval 11 1574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1574 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1574) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1574 : oddCount 1574 11 = 6 ∧ acceleratedOrbit 11 1574 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1574 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1574) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1574.1, data_11_1574.2]

/-- Complete interval computation for depth 11, residue 1575. -/
theorem bounds_11_1575 : exactInterval 11 1575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1575 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1575) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1575 : oddCount 1575 11 = 5 ∧ acceleratedOrbit 11 1575 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1575 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1575) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1575.1, data_11_1575.2]

/-- Complete interval computation for depth 11, residue 1576. -/
theorem bounds_11_1576 : exactInterval 11 1576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1576 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1576) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1576 : oddCount 1576 11 = 2 ∧ acceleratedOrbit 11 1576 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1576 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1576) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1576.1, data_11_1576.2]

/-- Complete interval computation for depth 11, residue 1577. -/
theorem bounds_11_1577 : exactInterval 11 1577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1577 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1577) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1577 : oddCount 1577 11 = 9 ∧ acceleratedOrbit 11 1577 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1577 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1577) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1577.1, data_11_1577.2]

/-- Complete interval computation for depth 11, residue 1578. -/
theorem bounds_11_1578 : exactInterval 11 1578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1578 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1578) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1578 : oddCount 1578 11 = 2 ∧ acceleratedOrbit 11 1578 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1578 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1578) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1578.1, data_11_1578.2]

/-- Complete interval computation for depth 11, residue 1579. -/
theorem bounds_11_1579 : exactInterval 11 1579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1579 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1579) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1579 : oddCount 1579 11 = 5 ∧ acceleratedOrbit 11 1579 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1579 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1579) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1579.1, data_11_1579.2]

/-- Complete interval computation for depth 11, residue 1580. -/
theorem bounds_11_1580 : exactInterval 11 1580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1580 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1580) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1580 : oddCount 1580 11 = 6 ∧ acceleratedOrbit 11 1580 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1580 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1580) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1580.1, data_11_1580.2]

/-- Complete interval computation for depth 11, residue 1581. -/
theorem bounds_11_1581 : exactInterval 11 1581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1581 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1581) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1581 : oddCount 1581 11 = 6 ∧ acceleratedOrbit 11 1581 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1581 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1581) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1581.1, data_11_1581.2]

/-- Complete interval computation for depth 11, residue 1582. -/
theorem bounds_11_1582 : exactInterval 11 1582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1582 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1582) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1582 : oddCount 1582 11 = 6 ∧ acceleratedOrbit 11 1582 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1582 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1582) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1582.1, data_11_1582.2]

/-- Complete interval computation for depth 11, residue 1583. -/
theorem bounds_11_1583 : exactInterval 11 1583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1583 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1583) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1583 : oddCount 1583 11 = 9 ∧ acceleratedOrbit 11 1583 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1583 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1583) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1583.1, data_11_1583.2]

/-- Complete interval computation for depth 11, residue 1584. -/
theorem bounds_11_1584 : exactInterval 11 1584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1584 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1584) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1584 : oddCount 1584 11 = 2 ∧ acceleratedOrbit 11 1584 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1584 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1584) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1584.1, data_11_1584.2]

/-- Complete interval computation for depth 11, residue 1585. -/
theorem bounds_11_1585 : exactInterval 11 1585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1585 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1585) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1585 : oddCount 1585 11 = 7 ∧ acceleratedOrbit 11 1585 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1585 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1585) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1585.1, data_11_1585.2]

/-- Complete interval computation for depth 11, residue 1586. -/
theorem bounds_11_1586 : exactInterval 11 1586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1586 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1586) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1586 : oddCount 1586 11 = 7 ∧ acceleratedOrbit 11 1586 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1586 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1586) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1586.1, data_11_1586.2]

end Collatz.Research.StoppingAtlas.Batch0170
