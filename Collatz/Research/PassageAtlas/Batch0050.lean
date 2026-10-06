import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0050

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1605. -/
theorem bounds_15_1605 : exactInterval 15 1605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1605 : oddCount 1605 15 = 4 ∧ acceleratedOrbit 15 1605 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1605) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1605.1, data_15_1605.2]

/-- Complete interval computation for depth 15, residue 1606. -/
theorem bounds_15_1606 : exactInterval 15 1606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1606 : oddCount 1606 15 = 4 ∧ acceleratedOrbit 15 1606 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1606) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1606.1, data_15_1606.2]

/-- Complete interval computation for depth 15, residue 1607. -/
theorem bounds_15_1607 : exactInterval 15 1607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1607 : oddCount 1607 15 = 9 ∧ acceleratedOrbit 15 1607 = 967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1607) = 3 ^ 9 * m + 967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1607.1, data_15_1607.2]

/-- Complete interval computation for depth 15, residue 1608. -/
theorem bounds_15_1608 : exactInterval 15 1608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1608 : oddCount 1608 15 = 4 ∧ acceleratedOrbit 15 1608 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1608) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1608.1, data_15_1608.2]

/-- Complete interval computation for depth 15, residue 1609. -/
theorem bounds_15_1609 : exactInterval 15 1609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1609 : oddCount 1609 15 = 10 ∧ acceleratedOrbit 15 1609 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1609) = 3 ^ 10 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1609.1, data_15_1609.2]

/-- Complete interval computation for depth 15, residue 1610. -/
theorem bounds_15_1610 : exactInterval 15 1610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1610 : oddCount 1610 15 = 4 ∧ acceleratedOrbit 15 1610 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1610) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1610.1, data_15_1610.2]

/-- Complete interval computation for depth 15, residue 1611. -/
theorem bounds_15_1611 : exactInterval 15 1611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1611 : oddCount 1611 15 = 4 ∧ acceleratedOrbit 15 1611 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1611) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1611.1, data_15_1611.2]

/-- Complete interval computation for depth 15, residue 1612. -/
theorem bounds_15_1612 : exactInterval 15 1612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1612 : oddCount 1612 15 = 4 ∧ acceleratedOrbit 15 1612 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1612) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1612.1, data_15_1612.2]

/-- Complete interval computation for depth 15, residue 1613. -/
theorem bounds_15_1613 : exactInterval 15 1613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1613 : oddCount 1613 15 = 4 ∧ acceleratedOrbit 15 1613 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1613) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1613.1, data_15_1613.2]

/-- Complete interval computation for depth 15, residue 1614. -/
theorem bounds_15_1614 : exactInterval 15 1614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1614 : oddCount 1614 15 = 11 ∧ acceleratedOrbit 15 1614 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1614) = 3 ^ 11 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1614.1, data_15_1614.2]

/-- Complete interval computation for depth 15, residue 1615. -/
theorem bounds_15_1615 : exactInterval 15 1615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1615 : oddCount 1615 15 = 11 ∧ acceleratedOrbit 15 1615 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1615) = 3 ^ 11 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1615.1, data_15_1615.2]

/-- Complete interval computation for depth 15, residue 1616. -/
theorem bounds_15_1616 : exactInterval 15 1616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1616 : oddCount 1616 15 = 5 ∧ acceleratedOrbit 15 1616 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1616) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1616.1, data_15_1616.2]

/-- Complete interval computation for depth 15, residue 1617. -/
theorem bounds_15_1617 : exactInterval 15 1617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1617 : oddCount 1617 15 = 8 ∧ acceleratedOrbit 15 1617 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1617) = 3 ^ 8 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1617.1, data_15_1617.2]

/-- Complete interval computation for depth 15, residue 1618. -/
theorem bounds_15_1618 : exactInterval 15 1618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1618 : oddCount 1618 15 = 8 ∧ acceleratedOrbit 15 1618 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1618) = 3 ^ 8 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1618.1, data_15_1618.2]

/-- Complete interval computation for depth 15, residue 1619. -/
theorem bounds_15_1619 : exactInterval 15 1619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1619 : oddCount 1619 15 = 8 ∧ acceleratedOrbit 15 1619 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1619) = 3 ^ 8 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1619.1, data_15_1619.2]

/-- Complete interval computation for depth 15, residue 1620. -/
theorem bounds_15_1620 : exactInterval 15 1620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1620 : oddCount 1620 15 = 5 ∧ acceleratedOrbit 15 1620 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1620) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1620.1, data_15_1620.2]

/-- Complete interval computation for depth 15, residue 1621. -/
theorem bounds_15_1621 : exactInterval 15 1621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1621 : oddCount 1621 15 = 5 ∧ acceleratedOrbit 15 1621 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1621) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1621.1, data_15_1621.2]

/-- Complete interval computation for depth 15, residue 1622. -/
theorem bounds_15_1622 : exactInterval 15 1622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1622 : oddCount 1622 15 = 7 ∧ acceleratedOrbit 15 1622 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1622) = 3 ^ 7 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1622.1, data_15_1622.2]

/-- Complete interval computation for depth 15, residue 1623. -/
theorem bounds_15_1623 : exactInterval 15 1623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1623 : oddCount 1623 15 = 7 ∧ acceleratedOrbit 15 1623 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1623) = 3 ^ 7 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1623.1, data_15_1623.2]

/-- Complete interval computation for depth 15, residue 1624. -/
theorem bounds_15_1624 : exactInterval 15 1624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1624 : oddCount 1624 15 = 6 ∧ acceleratedOrbit 15 1624 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1624) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1624.1, data_15_1624.2]

/-- Complete interval computation for depth 15, residue 1625. -/
theorem bounds_15_1625 : exactInterval 15 1625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1625 : oddCount 1625 15 = 7 ∧ acceleratedOrbit 15 1625 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1625) = 3 ^ 7 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1625.1, data_15_1625.2]

/-- Complete interval computation for depth 15, residue 1626. -/
theorem bounds_15_1626 : exactInterval 15 1626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1626 : oddCount 1626 15 = 6 ∧ acceleratedOrbit 15 1626 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1626) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1626.1, data_15_1626.2]

/-- Complete interval computation for depth 15, residue 1627. -/
theorem bounds_15_1627 : exactInterval 15 1627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1627 : oddCount 1627 15 = 10 ∧ acceleratedOrbit 15 1627 = 2936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1627) = 3 ^ 10 * m + 2936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1627.1, data_15_1627.2]

/-- Complete interval computation for depth 15, residue 1628. -/
theorem bounds_15_1628 : exactInterval 15 1628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1628 : oddCount 1628 15 = 6 ∧ acceleratedOrbit 15 1628 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1628) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1628.1, data_15_1628.2]

/-- Complete interval computation for depth 15, residue 1629. -/
theorem bounds_15_1629 : exactInterval 15 1629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1629 : oddCount 1629 15 = 6 ∧ acceleratedOrbit 15 1629 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1629) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1629.1, data_15_1629.2]

/-- Complete interval computation for depth 15, residue 1630. -/
theorem bounds_15_1630 : exactInterval 15 1630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1630 : oddCount 1630 15 = 7 ∧ acceleratedOrbit 15 1630 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1630) = 3 ^ 7 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1630.1, data_15_1630.2]

/-- Complete interval computation for depth 15, residue 1631. -/
theorem bounds_15_1631 : exactInterval 15 1631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1631 : oddCount 1631 15 = 7 ∧ acceleratedOrbit 15 1631 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1631) = 3 ^ 7 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1631.1, data_15_1631.2]

/-- Complete interval computation for depth 15, residue 1632. -/
theorem bounds_15_1632 : exactInterval 15 1632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1632 : oddCount 1632 15 = 5 ∧ acceleratedOrbit 15 1632 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1632) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1632.1, data_15_1632.2]

/-- Complete interval computation for depth 15, residue 1633. -/
theorem bounds_15_1633 : exactInterval 15 1633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1633 : oddCount 1633 15 = 7 ∧ acceleratedOrbit 15 1633 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1633) = 3 ^ 7 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1633.1, data_15_1633.2]

/-- Complete interval computation for depth 15, residue 1634. -/
theorem bounds_15_1634 : exactInterval 15 1634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1634 : oddCount 1634 15 = 6 ∧ acceleratedOrbit 15 1634 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1634) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1634.1, data_15_1634.2]

/-- Complete interval computation for depth 15, residue 1635. -/
theorem bounds_15_1635 : exactInterval 15 1635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1635 : oddCount 1635 15 = 6 ∧ acceleratedOrbit 15 1635 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1635) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1635.1, data_15_1635.2]

/-- Complete interval computation for depth 15, residue 1636. -/
theorem bounds_15_1636 : exactInterval 15 1636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1636 : oddCount 1636 15 = 6 ∧ acceleratedOrbit 15 1636 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1636) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1636.1, data_15_1636.2]

/-- Complete interval computation for depth 15, residue 1637. -/
theorem bounds_15_1637 : exactInterval 15 1637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1637 : oddCount 1637 15 = 6 ∧ acceleratedOrbit 15 1637 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1637) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1637.1, data_15_1637.2]

end Collatz.Research.PassageAtlas.Batch0050
