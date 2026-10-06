import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0049

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1572. -/
theorem bounds_15_1572 : exactInterval 15 1572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1572 : oddCount 1572 15 = 8 ∧ acceleratedOrbit 15 1572 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1572) = 3 ^ 8 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1572.1, data_15_1572.2]

/-- Complete interval computation for depth 15, residue 1573. -/
theorem bounds_15_1573 : exactInterval 15 1573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1573 : oddCount 1573 15 = 8 ∧ acceleratedOrbit 15 1573 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1573) = 3 ^ 8 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1573.1, data_15_1573.2]

/-- Complete interval computation for depth 15, residue 1574. -/
theorem bounds_15_1574 : exactInterval 15 1574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1574 : oddCount 1574 15 = 8 ∧ acceleratedOrbit 15 1574 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1574) = 3 ^ 8 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1574.1, data_15_1574.2]

/-- Complete interval computation for depth 15, residue 1575. -/
theorem bounds_15_1575 : exactInterval 15 1575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1575 : oddCount 1575 15 = 8 ∧ acceleratedOrbit 15 1575 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1575) = 3 ^ 8 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1575.1, data_15_1575.2]

/-- Complete interval computation for depth 15, residue 1576. -/
theorem bounds_15_1576 : exactInterval 15 1576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1576 : oddCount 1576 15 = 5 ∧ acceleratedOrbit 15 1576 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1576) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1576.1, data_15_1576.2]

/-- Complete interval computation for depth 15, residue 1577. -/
theorem bounds_15_1577 : exactInterval 15 1577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1577 : oddCount 1577 15 = 10 ∧ acceleratedOrbit 15 1577 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1577) = 3 ^ 10 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1577.1, data_15_1577.2]

/-- Complete interval computation for depth 15, residue 1578. -/
theorem bounds_15_1578 : exactInterval 15 1578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1578 : oddCount 1578 15 = 5 ∧ acceleratedOrbit 15 1578 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1578) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1578.1, data_15_1578.2]

/-- Complete interval computation for depth 15, residue 1579. -/
theorem bounds_15_1579 : exactInterval 15 1579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1579 : oddCount 1579 15 = 7 ∧ acceleratedOrbit 15 1579 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1579) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1579.1, data_15_1579.2]

/-- Complete interval computation for depth 15, residue 1580. -/
theorem bounds_15_1580 : exactInterval 15 1580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1580 : oddCount 1580 15 = 8 ∧ acceleratedOrbit 15 1580 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1580) = 3 ^ 8 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1580.1, data_15_1580.2]

/-- Complete interval computation for depth 15, residue 1581. -/
theorem bounds_15_1581 : exactInterval 15 1581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1581 : oddCount 1581 15 = 8 ∧ acceleratedOrbit 15 1581 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1581) = 3 ^ 8 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1581.1, data_15_1581.2]

/-- Complete interval computation for depth 15, residue 1582. -/
theorem bounds_15_1582 : exactInterval 15 1582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1582 : oddCount 1582 15 = 8 ∧ acceleratedOrbit 15 1582 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1582) = 3 ^ 8 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1582.1, data_15_1582.2]

/-- Complete interval computation for depth 15, residue 1583. -/
theorem bounds_15_1583 : exactInterval 15 1583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1583 : oddCount 1583 15 = 12 ∧ acceleratedOrbit 15 1583 = 25697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1583) = 3 ^ 12 * m + 25697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1583.1, data_15_1583.2]

/-- Complete interval computation for depth 15, residue 1584. -/
theorem bounds_15_1584 : exactInterval 15 1584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1584 : oddCount 1584 15 = 5 ∧ acceleratedOrbit 15 1584 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1584) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1584.1, data_15_1584.2]

/-- Complete interval computation for depth 15, residue 1585. -/
theorem bounds_15_1585 : exactInterval 15 1585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1585 : oddCount 1585 15 = 8 ∧ acceleratedOrbit 15 1585 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1585) = 3 ^ 8 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1585.1, data_15_1585.2]

/-- Complete interval computation for depth 15, residue 1586. -/
theorem bounds_15_1586 : exactInterval 15 1586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1586 : oddCount 1586 15 = 8 ∧ acceleratedOrbit 15 1586 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1586) = 3 ^ 8 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1586.1, data_15_1586.2]

/-- Complete interval computation for depth 15, residue 1587. -/
theorem bounds_15_1587 : exactInterval 15 1587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1587 : oddCount 1587 15 = 8 ∧ acceleratedOrbit 15 1587 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1587) = 3 ^ 8 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1587.1, data_15_1587.2]

/-- Complete interval computation for depth 15, residue 1588. -/
theorem bounds_15_1588 : exactInterval 15 1588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1588 : oddCount 1588 15 = 5 ∧ acceleratedOrbit 15 1588 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1588) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1588.1, data_15_1588.2]

/-- Complete interval computation for depth 15, residue 1589. -/
theorem bounds_15_1589 : exactInterval 15 1589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1589 : oddCount 1589 15 = 5 ∧ acceleratedOrbit 15 1589 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1589) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1589.1, data_15_1589.2]

/-- Complete interval computation for depth 15, residue 1590. -/
theorem bounds_15_1590 : exactInterval 15 1590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1590 : oddCount 1590 15 = 11 ∧ acceleratedOrbit 15 1590 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1590) = 3 ^ 11 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1590.1, data_15_1590.2]

/-- Complete interval computation for depth 15, residue 1591. -/
theorem bounds_15_1591 : exactInterval 15 1591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1591 : oddCount 1591 15 = 11 ∧ acceleratedOrbit 15 1591 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1591) = 3 ^ 11 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1591.1, data_15_1591.2]

/-- Complete interval computation for depth 15, residue 1592. -/
theorem bounds_15_1592 : exactInterval 15 1592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1592 : oddCount 1592 15 = 8 ∧ acceleratedOrbit 15 1592 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1592) = 3 ^ 8 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1592.1, data_15_1592.2]

/-- Complete interval computation for depth 15, residue 1593. -/
theorem bounds_15_1593 : exactInterval 15 1593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1593 : oddCount 1593 15 = 7 ∧ acceleratedOrbit 15 1593 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1593) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1593.1, data_15_1593.2]

/-- Complete interval computation for depth 15, residue 1594. -/
theorem bounds_15_1594 : exactInterval 15 1594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1594 : oddCount 1594 15 = 8 ∧ acceleratedOrbit 15 1594 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1594) = 3 ^ 8 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1594.1, data_15_1594.2]

/-- Complete interval computation for depth 15, residue 1595. -/
theorem bounds_15_1595 : exactInterval 15 1595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1595 : oddCount 1595 15 = 9 ∧ acceleratedOrbit 15 1595 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1595) = 3 ^ 9 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1595.1, data_15_1595.2]

/-- Complete interval computation for depth 15, residue 1596. -/
theorem bounds_15_1596 : exactInterval 15 1596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1596 : oddCount 1596 15 = 8 ∧ acceleratedOrbit 15 1596 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1596) = 3 ^ 8 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1596.1, data_15_1596.2]

/-- Complete interval computation for depth 15, residue 1597. -/
theorem bounds_15_1597 : exactInterval 15 1597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1597 : oddCount 1597 15 = 8 ∧ acceleratedOrbit 15 1597 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1597) = 3 ^ 8 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1597.1, data_15_1597.2]

/-- Complete interval computation for depth 15, residue 1598. -/
theorem bounds_15_1598 : exactInterval 15 1598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1598 : oddCount 1598 15 = 9 ∧ acceleratedOrbit 15 1598 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1598) = 3 ^ 9 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1598.1, data_15_1598.2]

/-- Complete interval computation for depth 15, residue 1599. -/
theorem bounds_15_1599 : exactInterval 15 1599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1599 : oddCount 1599 15 = 9 ∧ acceleratedOrbit 15 1599 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1599) = 3 ^ 9 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1599.1, data_15_1599.2]

/-- Complete interval computation for depth 15, residue 1600. -/
theorem bounds_15_1600 : exactInterval 15 1600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1600 : oddCount 1600 15 = 5 ∧ acceleratedOrbit 15 1600 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1600) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1600.1, data_15_1600.2]

/-- Complete interval computation for depth 15, residue 1601. -/
theorem bounds_15_1601 : exactInterval 15 1601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1601 : oddCount 1601 15 = 9 ∧ acceleratedOrbit 15 1601 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1601) = 3 ^ 9 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1601.1, data_15_1601.2]

/-- Complete interval computation for depth 15, residue 1602. -/
theorem bounds_15_1602 : exactInterval 15 1602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1602 : oddCount 1602 15 = 9 ∧ acceleratedOrbit 15 1602 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1602) = 3 ^ 9 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1602.1, data_15_1602.2]

/-- Complete interval computation for depth 15, residue 1603. -/
theorem bounds_15_1603 : exactInterval 15 1603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1603 : oddCount 1603 15 = 9 ∧ acceleratedOrbit 15 1603 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1603) = 3 ^ 9 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1603.1, data_15_1603.2]

/-- Complete interval computation for depth 15, residue 1604. -/
theorem bounds_15_1604 : exactInterval 15 1604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1604 : oddCount 1604 15 = 4 ∧ acceleratedOrbit 15 1604 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1604) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1604.1, data_15_1604.2]

end Collatz.Research.PassageAtlas.Batch0049
