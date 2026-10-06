import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0573

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1617. -/
theorem bounds_13_1617 : exactInterval 13 1617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1617 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1617) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1617 : oddCount 1617 13 = 7 ∧ acceleratedOrbit 13 1617 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1617 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1617) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1617.1, data_13_1617.2]

/-- Complete interval computation for depth 13, residue 1618. -/
theorem bounds_13_1618 : exactInterval 13 1618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1618 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1618) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1618 : oddCount 1618 13 = 7 ∧ acceleratedOrbit 13 1618 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1618 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1618) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1618.1, data_13_1618.2]

/-- Complete interval computation for depth 13, residue 1619. -/
theorem bounds_13_1619 : exactInterval 13 1619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1619 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1619) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1619 : oddCount 1619 13 = 7 ∧ acceleratedOrbit 13 1619 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1619 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1619) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1619.1, data_13_1619.2]

/-- Complete interval computation for depth 13, residue 1620. -/
theorem bounds_13_1620 : exactInterval 13 1620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1620 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1620) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1620 : oddCount 1620 13 = 4 ∧ acceleratedOrbit 13 1620 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1620 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1620) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1620.1, data_13_1620.2]

/-- Complete interval computation for depth 13, residue 1621. -/
theorem bounds_13_1621 : exactInterval 13 1621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1621 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1621) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1621 : oddCount 1621 13 = 4 ∧ acceleratedOrbit 13 1621 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1621 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1621) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1621.1, data_13_1621.2]

/-- Complete interval computation for depth 13, residue 1622. -/
theorem bounds_13_1622 : exactInterval 13 1622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1622 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1622) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1622 : oddCount 1622 13 = 6 ∧ acceleratedOrbit 13 1622 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1622 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1622) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1622.1, data_13_1622.2]

/-- Complete interval computation for depth 13, residue 1623. -/
theorem bounds_13_1623 : exactInterval 13 1623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1623 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1623) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1623 : oddCount 1623 13 = 6 ∧ acceleratedOrbit 13 1623 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1623 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1623) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1623.1, data_13_1623.2]

/-- Complete interval computation for depth 13, residue 1624. -/
theorem bounds_13_1624 : exactInterval 13 1624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1624 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1624) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1624 : oddCount 1624 13 = 5 ∧ acceleratedOrbit 13 1624 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1624 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1624) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1624.1, data_13_1624.2]

/-- Complete interval computation for depth 13, residue 1625. -/
theorem bounds_13_1625 : exactInterval 13 1625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1625 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1625) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1625 : oddCount 1625 13 = 6 ∧ acceleratedOrbit 13 1625 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1625 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1625) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1625.1, data_13_1625.2]

/-- Complete interval computation for depth 13, residue 1626. -/
theorem bounds_13_1626 : exactInterval 13 1626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1626 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1626) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1626 : oddCount 1626 13 = 5 ∧ acceleratedOrbit 13 1626 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1626 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1626) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1626.1, data_13_1626.2]

/-- Complete interval computation for depth 13, residue 1627. -/
theorem bounds_13_1627 : exactInterval 13 1627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1627 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1627) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1627 : oddCount 1627 13 = 9 ∧ acceleratedOrbit 13 1627 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1627 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1627) = 3 ^ 9 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1627.1, data_13_1627.2]

/-- Complete interval computation for depth 13, residue 1628. -/
theorem bounds_13_1628 : exactInterval 13 1628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1628 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1628) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1628 : oddCount 1628 13 = 5 ∧ acceleratedOrbit 13 1628 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1628 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1628) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1628.1, data_13_1628.2]

/-- Complete interval computation for depth 13, residue 1629. -/
theorem bounds_13_1629 : exactInterval 13 1629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1629 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1629) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1629 : oddCount 1629 13 = 5 ∧ acceleratedOrbit 13 1629 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1629 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1629) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1629.1, data_13_1629.2]

/-- Complete interval computation for depth 13, residue 1630. -/
theorem bounds_13_1630 : exactInterval 13 1630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1630 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1630) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1630 : oddCount 1630 13 = 7 ∧ acceleratedOrbit 13 1630 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1630 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1630) = 3 ^ 7 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1630.1, data_13_1630.2]

/-- Complete interval computation for depth 13, residue 1631. -/
theorem bounds_13_1631 : exactInterval 13 1631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1631 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1631) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1631 : oddCount 1631 13 = 7 ∧ acceleratedOrbit 13 1631 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1631 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1631) = 3 ^ 7 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1631.1, data_13_1631.2]

/-- Complete interval computation for depth 13, residue 1632. -/
theorem bounds_13_1632 : exactInterval 13 1632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1632 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1632) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1632 : oddCount 1632 13 = 4 ∧ acceleratedOrbit 13 1632 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1632 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1632) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1632.1, data_13_1632.2]

end Collatz.Research.StoppingAtlas.Batch0573
