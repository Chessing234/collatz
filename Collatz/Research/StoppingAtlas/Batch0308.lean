import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0308

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1643. -/
theorem bounds_12_1643 : exactInterval 12 1643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1643 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1643) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1643 : oddCount 1643 12 = 8 ∧ acceleratedOrbit 12 1643 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1643 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1643) = 3 ^ 8 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1643.1, data_12_1643.2]

/-- Complete interval computation for depth 12, residue 1644. -/
theorem bounds_12_1644 : exactInterval 12 1644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1644 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1644) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1644 : oddCount 1644 12 = 7 ∧ acceleratedOrbit 12 1644 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1644 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1644) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1644.1, data_12_1644.2]

/-- Complete interval computation for depth 12, residue 1645. -/
theorem bounds_12_1645 : exactInterval 12 1645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1645 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1645) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1645 : oddCount 1645 12 = 7 ∧ acceleratedOrbit 12 1645 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1645 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1645) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1645.1, data_12_1645.2]

/-- Complete interval computation for depth 12, residue 1646. -/
theorem bounds_12_1646 : exactInterval 12 1646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1646 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1646) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1646 : oddCount 1646 12 = 7 ∧ acceleratedOrbit 12 1646 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1646 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1646) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1646.1, data_12_1646.2]

/-- Complete interval computation for depth 12, residue 1647. -/
theorem bounds_12_1647 : exactInterval 12 1647 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1647 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1647) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1647 : oddCount 1647 12 = 7 ∧ acceleratedOrbit 12 1647 = 880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1647 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1647) = 3 ^ 7 * m + 880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1647.1, data_12_1647.2]

/-- Complete interval computation for depth 12, residue 1648. -/
theorem bounds_12_1648 : exactInterval 12 1648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1648 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1648) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1648 : oddCount 1648 12 = 7 ∧ acceleratedOrbit 12 1648 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1648 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1648) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1648.1, data_12_1648.2]

/-- Complete interval computation for depth 12, residue 1649. -/
theorem bounds_12_1649 : exactInterval 12 1649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1649 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1649) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1649 : oddCount 1649 12 = 3 ∧ acceleratedOrbit 12 1649 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1649 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1649) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1649.1, data_12_1649.2]

/-- Complete interval computation for depth 12, residue 1650. -/
theorem bounds_12_1650 : exactInterval 12 1650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1650 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1650) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1650 : oddCount 1650 12 = 7 ∧ acceleratedOrbit 12 1650 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1650 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1650) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1650.1, data_12_1650.2]

/-- Complete interval computation for depth 12, residue 1651. -/
theorem bounds_12_1651 : exactInterval 12 1651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1651 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1651) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1651 : oddCount 1651 12 = 7 ∧ acceleratedOrbit 12 1651 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1651 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1651) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1651.1, data_12_1651.2]

/-- Complete interval computation for depth 12, residue 1652. -/
theorem bounds_12_1652 : exactInterval 12 1652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1652 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1652) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1652 : oddCount 1652 12 = 7 ∧ acceleratedOrbit 12 1652 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1652 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1652) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1652.1, data_12_1652.2]

/-- Complete interval computation for depth 12, residue 1653. -/
theorem bounds_12_1653 : exactInterval 12 1653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1653 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1653) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1653 : oddCount 1653 12 = 7 ∧ acceleratedOrbit 12 1653 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1653 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1653) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1653.1, data_12_1653.2]

/-- Complete interval computation for depth 12, residue 1654. -/
theorem bounds_12_1654 : exactInterval 12 1654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1654 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1654) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1654 : oddCount 1654 12 = 6 ∧ acceleratedOrbit 12 1654 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1654 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1654) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1654.1, data_12_1654.2]

/-- Complete interval computation for depth 12, residue 1655. -/
theorem bounds_12_1655 : exactInterval 12 1655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1655 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1655) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1655 : oddCount 1655 12 = 6 ∧ acceleratedOrbit 12 1655 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1655 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1655) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1655.1, data_12_1655.2]

/-- Complete interval computation for depth 12, residue 1656. -/
theorem bounds_12_1656 : exactInterval 12 1656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1656 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1656) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1656 : oddCount 1656 12 = 7 ∧ acceleratedOrbit 12 1656 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1656 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1656) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1656.1, data_12_1656.2]

/-- Complete interval computation for depth 12, residue 1657. -/
theorem bounds_12_1657 : exactInterval 12 1657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1657 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1657) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1657 : oddCount 1657 12 = 7 ∧ acceleratedOrbit 12 1657 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1657 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1657) = 3 ^ 7 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1657.1, data_12_1657.2]

end Collatz.Research.StoppingAtlas.Batch0308
