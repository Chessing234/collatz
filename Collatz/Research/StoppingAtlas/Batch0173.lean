import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0173

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1617. -/
theorem bounds_11_1617 : exactInterval 11 1617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1617 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1617) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1617 : oddCount 1617 11 = 6 ∧ acceleratedOrbit 11 1617 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1617 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1617) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1617.1, data_11_1617.2]

/-- Complete interval computation for depth 11, residue 1618. -/
theorem bounds_11_1618 : exactInterval 11 1618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1618 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1618) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1618 : oddCount 1618 11 = 6 ∧ acceleratedOrbit 11 1618 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1618 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1618) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1618.1, data_11_1618.2]

/-- Complete interval computation for depth 11, residue 1619. -/
theorem bounds_11_1619 : exactInterval 11 1619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1619 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1619) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1619 : oddCount 1619 11 = 6 ∧ acceleratedOrbit 11 1619 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1619 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1619) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1619.1, data_11_1619.2]

/-- Complete interval computation for depth 11, residue 1620. -/
theorem bounds_11_1620 : exactInterval 11 1620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1620 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1620) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1620 : oddCount 1620 11 = 3 ∧ acceleratedOrbit 11 1620 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1620 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1620) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1620.1, data_11_1620.2]

/-- Complete interval computation for depth 11, residue 1621. -/
theorem bounds_11_1621 : exactInterval 11 1621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1621 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1621) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1621 : oddCount 1621 11 = 3 ∧ acceleratedOrbit 11 1621 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1621 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1621) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1621.1, data_11_1621.2]

/-- Complete interval computation for depth 11, residue 1622. -/
theorem bounds_11_1622 : exactInterval 11 1622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1622 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1622) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1622 : oddCount 1622 11 = 5 ∧ acceleratedOrbit 11 1622 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1622 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1622) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1622.1, data_11_1622.2]

/-- Complete interval computation for depth 11, residue 1623. -/
theorem bounds_11_1623 : exactInterval 11 1623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1623 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1623) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1623 : oddCount 1623 11 = 5 ∧ acceleratedOrbit 11 1623 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1623 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1623) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1623.1, data_11_1623.2]

/-- Complete interval computation for depth 11, residue 1624. -/
theorem bounds_11_1624 : exactInterval 11 1624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1624 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1624) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1624 : oddCount 1624 11 = 4 ∧ acceleratedOrbit 11 1624 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1624 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1624) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1624.1, data_11_1624.2]

/-- Complete interval computation for depth 11, residue 1625. -/
theorem bounds_11_1625 : exactInterval 11 1625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1625 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1625) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1625 : oddCount 1625 11 = 6 ∧ acceleratedOrbit 11 1625 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1625 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1625) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1625.1, data_11_1625.2]

/-- Complete interval computation for depth 11, residue 1626. -/
theorem bounds_11_1626 : exactInterval 11 1626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1626 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1626) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1626 : oddCount 1626 11 = 4 ∧ acceleratedOrbit 11 1626 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1626 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1626) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1626.1, data_11_1626.2]

/-- Complete interval computation for depth 11, residue 1627. -/
theorem bounds_11_1627 : exactInterval 11 1627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1627 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1627) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1627 : oddCount 1627 11 = 7 ∧ acceleratedOrbit 11 1627 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1627 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1627) = 3 ^ 7 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1627.1, data_11_1627.2]

/-- Complete interval computation for depth 11, residue 1628. -/
theorem bounds_11_1628 : exactInterval 11 1628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1628 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1628) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1628 : oddCount 1628 11 = 4 ∧ acceleratedOrbit 11 1628 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1628 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1628) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1628.1, data_11_1628.2]

/-- Complete interval computation for depth 11, residue 1629. -/
theorem bounds_11_1629 : exactInterval 11 1629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1629 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1629) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1629 : oddCount 1629 11 = 4 ∧ acceleratedOrbit 11 1629 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1629 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1629) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1629.1, data_11_1629.2]

/-- Complete interval computation for depth 11, residue 1630. -/
theorem bounds_11_1630 : exactInterval 11 1630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1630 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1630) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1630 : oddCount 1630 11 = 6 ∧ acceleratedOrbit 11 1630 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1630 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1630) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1630.1, data_11_1630.2]

/-- Complete interval computation for depth 11, residue 1631. -/
theorem bounds_11_1631 : exactInterval 11 1631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1631 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1631) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1631 : oddCount 1631 11 = 6 ∧ acceleratedOrbit 11 1631 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1631 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1631) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1631.1, data_11_1631.2]

/-- Complete interval computation for depth 11, residue 1632. -/
theorem bounds_11_1632 : exactInterval 11 1632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1632 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1632) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1632 : oddCount 1632 11 = 3 ∧ acceleratedOrbit 11 1632 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1632 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1632) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1632.1, data_11_1632.2]

end Collatz.Research.StoppingAtlas.Batch0173
