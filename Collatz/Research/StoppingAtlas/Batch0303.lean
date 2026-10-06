import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0303

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1566. -/
theorem bounds_12_1566 : exactInterval 12 1566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1566 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1566) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1566 : oddCount 1566 12 = 4 ∧ acceleratedOrbit 12 1566 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1566 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1566) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1566.1, data_12_1566.2]

/-- Complete interval computation for depth 12, residue 1567. -/
theorem bounds_12_1567 : exactInterval 12 1567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1567 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1567) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1567 : oddCount 1567 12 = 8 ∧ acceleratedOrbit 12 1567 = 2512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1567 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1567) = 3 ^ 8 * m + 2512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1567.1, data_12_1567.2]

/-- Complete interval computation for depth 12, residue 1568. -/
theorem bounds_12_1568 : exactInterval 12 1568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1568 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1568) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1568 : oddCount 1568 12 = 3 ∧ acceleratedOrbit 12 1568 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1568 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1568) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1568.1, data_12_1568.2]

/-- Complete interval computation for depth 12, residue 1569. -/
theorem bounds_12_1569 : exactInterval 12 1569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1569 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1569) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1569 : oddCount 1569 12 = 6 ∧ acceleratedOrbit 12 1569 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1569 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1569) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1569.1, data_12_1569.2]

/-- Complete interval computation for depth 12, residue 1570. -/
theorem bounds_12_1570 : exactInterval 12 1570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1570 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1570) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1570 : oddCount 1570 12 = 5 ∧ acceleratedOrbit 12 1570 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1570 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1570) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1570.1, data_12_1570.2]

/-- Complete interval computation for depth 12, residue 1571. -/
theorem bounds_12_1571 : exactInterval 12 1571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1571 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1571) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1571 : oddCount 1571 12 = 5 ∧ acceleratedOrbit 12 1571 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1571 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1571) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1571.1, data_12_1571.2]

/-- Complete interval computation for depth 12, residue 1572. -/
theorem bounds_12_1572 : exactInterval 12 1572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1572 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1572) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1572 : oddCount 1572 12 = 6 ∧ acceleratedOrbit 12 1572 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1572 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1572) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1572.1, data_12_1572.2]

/-- Complete interval computation for depth 12, residue 1573. -/
theorem bounds_12_1573 : exactInterval 12 1573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1573 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1573) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1573 : oddCount 1573 12 = 6 ∧ acceleratedOrbit 12 1573 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1573 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1573) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1573.1, data_12_1573.2]

/-- Complete interval computation for depth 12, residue 1574. -/
theorem bounds_12_1574 : exactInterval 12 1574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1574 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1574) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1574 : oddCount 1574 12 = 6 ∧ acceleratedOrbit 12 1574 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1574 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1574) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1574.1, data_12_1574.2]

/-- Complete interval computation for depth 12, residue 1575. -/
theorem bounds_12_1575 : exactInterval 12 1575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1575 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1575) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1575 : oddCount 1575 12 = 6 ∧ acceleratedOrbit 12 1575 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1575 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1575) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1575.1, data_12_1575.2]

/-- Complete interval computation for depth 12, residue 1576. -/
theorem bounds_12_1576 : exactInterval 12 1576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1576 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1576) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1576 : oddCount 1576 12 = 3 ∧ acceleratedOrbit 12 1576 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1576 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1576) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1576.1, data_12_1576.2]

/-- Complete interval computation for depth 12, residue 1577. -/
theorem bounds_12_1577 : exactInterval 12 1577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1577 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1577) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1577 : oddCount 1577 12 = 10 ∧ acceleratedOrbit 12 1577 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1577 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1577) = 3 ^ 10 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1577.1, data_12_1577.2]

/-- Complete interval computation for depth 12, residue 1578. -/
theorem bounds_12_1578 : exactInterval 12 1578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1578 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1578) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1578 : oddCount 1578 12 = 3 ∧ acceleratedOrbit 12 1578 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1578 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1578) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1578.1, data_12_1578.2]

/-- Complete interval computation for depth 12, residue 1579. -/
theorem bounds_12_1579 : exactInterval 12 1579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1579 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1579) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1579 : oddCount 1579 12 = 5 ∧ acceleratedOrbit 12 1579 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1579 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1579) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1579.1, data_12_1579.2]

/-- Complete interval computation for depth 12, residue 1580. -/
theorem bounds_12_1580 : exactInterval 12 1580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1580 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1580) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1580 : oddCount 1580 12 = 6 ∧ acceleratedOrbit 12 1580 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1580 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1580) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1580.1, data_12_1580.2]

/-- Complete interval computation for depth 12, residue 1581. -/
theorem bounds_12_1581 : exactInterval 12 1581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1581 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1581) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1581 : oddCount 1581 12 = 6 ∧ acceleratedOrbit 12 1581 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1581 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1581) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1581.1, data_12_1581.2]

end Collatz.Research.StoppingAtlas.Batch0303
