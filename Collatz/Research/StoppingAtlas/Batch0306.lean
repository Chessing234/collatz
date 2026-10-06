import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0306

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1612. -/
theorem bounds_12_1612 : exactInterval 12 1612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1612 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1612) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1612 : oddCount 1612 12 = 4 ∧ acceleratedOrbit 12 1612 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1612 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1612) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1612.1, data_12_1612.2]

/-- Complete interval computation for depth 12, residue 1613. -/
theorem bounds_12_1613 : exactInterval 12 1613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1613 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1613) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1613 : oddCount 1613 12 = 4 ∧ acceleratedOrbit 12 1613 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1613 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1613) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1613.1, data_12_1613.2]

/-- Complete interval computation for depth 12, residue 1614. -/
theorem bounds_12_1614 : exactInterval 12 1614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1614 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1614) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1614 : oddCount 1614 12 = 8 ∧ acceleratedOrbit 12 1614 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1614 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1614) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1614.1, data_12_1614.2]

/-- Complete interval computation for depth 12, residue 1615. -/
theorem bounds_12_1615 : exactInterval 12 1615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1615 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1615) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1615 : oddCount 1615 12 = 8 ∧ acceleratedOrbit 12 1615 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1615 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1615) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1615.1, data_12_1615.2]

/-- Complete interval computation for depth 12, residue 1616. -/
theorem bounds_12_1616 : exactInterval 12 1616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1616 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1616) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1616 : oddCount 1616 12 = 3 ∧ acceleratedOrbit 12 1616 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1616 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1616) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1616.1, data_12_1616.2]

/-- Complete interval computation for depth 12, residue 1617. -/
theorem bounds_12_1617 : exactInterval 12 1617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1617 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1617) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1617 : oddCount 1617 12 = 7 ∧ acceleratedOrbit 12 1617 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1617 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1617) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1617.1, data_12_1617.2]

/-- Complete interval computation for depth 12, residue 1618. -/
theorem bounds_12_1618 : exactInterval 12 1618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1618 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1618) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1618 : oddCount 1618 12 = 7 ∧ acceleratedOrbit 12 1618 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1618 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1618) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1618.1, data_12_1618.2]

/-- Complete interval computation for depth 12, residue 1619. -/
theorem bounds_12_1619 : exactInterval 12 1619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1619 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1619) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1619 : oddCount 1619 12 = 7 ∧ acceleratedOrbit 12 1619 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1619 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1619) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1619.1, data_12_1619.2]

/-- Complete interval computation for depth 12, residue 1620. -/
theorem bounds_12_1620 : exactInterval 12 1620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1620 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1620) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1620 : oddCount 1620 12 = 3 ∧ acceleratedOrbit 12 1620 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1620 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1620) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1620.1, data_12_1620.2]

/-- Complete interval computation for depth 12, residue 1621. -/
theorem bounds_12_1621 : exactInterval 12 1621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1621 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1621) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1621 : oddCount 1621 12 = 3 ∧ acceleratedOrbit 12 1621 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1621 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1621) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1621.1, data_12_1621.2]

/-- Complete interval computation for depth 12, residue 1622. -/
theorem bounds_12_1622 : exactInterval 12 1622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1622 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1622) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1622 : oddCount 1622 12 = 6 ∧ acceleratedOrbit 12 1622 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1622 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1622) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1622.1, data_12_1622.2]

/-- Complete interval computation for depth 12, residue 1623. -/
theorem bounds_12_1623 : exactInterval 12 1623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1623 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1623) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1623 : oddCount 1623 12 = 6 ∧ acceleratedOrbit 12 1623 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1623 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1623) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1623.1, data_12_1623.2]

/-- Complete interval computation for depth 12, residue 1624. -/
theorem bounds_12_1624 : exactInterval 12 1624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1624 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1624) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1624 : oddCount 1624 12 = 5 ∧ acceleratedOrbit 12 1624 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1624 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1624) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1624.1, data_12_1624.2]

/-- Complete interval computation for depth 12, residue 1625. -/
theorem bounds_12_1625 : exactInterval 12 1625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1625 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1625) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1625 : oddCount 1625 12 = 6 ∧ acceleratedOrbit 12 1625 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1625 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1625) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1625.1, data_12_1625.2]

/-- Complete interval computation for depth 12, residue 1626. -/
theorem bounds_12_1626 : exactInterval 12 1626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1626 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1626) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1626 : oddCount 1626 12 = 5 ∧ acceleratedOrbit 12 1626 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1626 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1626) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1626.1, data_12_1626.2]

/-- Complete interval computation for depth 12, residue 1627. -/
theorem bounds_12_1627 : exactInterval 12 1627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1627 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1627) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1627 : oddCount 1627 12 = 8 ∧ acceleratedOrbit 12 1627 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1627 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1627) = 3 ^ 8 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1627.1, data_12_1627.2]

end Collatz.Research.StoppingAtlas.Batch0306
