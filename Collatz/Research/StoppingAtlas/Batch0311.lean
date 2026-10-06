import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0311

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1689. -/
theorem bounds_12_1689 : exactInterval 12 1689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1689 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1689) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1689 : oddCount 1689 12 = 7 ∧ acceleratedOrbit 12 1689 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1689 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1689) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1689.1, data_12_1689.2]

/-- Complete interval computation for depth 12, residue 1690. -/
theorem bounds_12_1690 : exactInterval 12 1690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1690 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1690) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1690 : oddCount 1690 12 = 5 ∧ acceleratedOrbit 12 1690 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1690 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1690) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1690.1, data_12_1690.2]

/-- Complete interval computation for depth 12, residue 1691. -/
theorem bounds_12_1691 : exactInterval 12 1691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1691 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1691) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1691 : oddCount 1691 12 = 8 ∧ acceleratedOrbit 12 1691 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1691 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1691) = 3 ^ 8 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1691.1, data_12_1691.2]

/-- Complete interval computation for depth 12, residue 1692. -/
theorem bounds_12_1692 : exactInterval 12 1692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1692 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1692) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1692 : oddCount 1692 12 = 6 ∧ acceleratedOrbit 12 1692 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1692 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1692) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1692.1, data_12_1692.2]

/-- Complete interval computation for depth 12, residue 1693. -/
theorem bounds_12_1693 : exactInterval 12 1693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1693 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1693) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1693 : oddCount 1693 12 = 6 ∧ acceleratedOrbit 12 1693 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1693 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1693) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1693.1, data_12_1693.2]

/-- Complete interval computation for depth 12, residue 1694. -/
theorem bounds_12_1694 : exactInterval 12 1694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1694 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1694) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1694 : oddCount 1694 12 = 6 ∧ acceleratedOrbit 12 1694 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1694 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1694) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1694.1, data_12_1694.2]

/-- Complete interval computation for depth 12, residue 1695. -/
theorem bounds_12_1695 : exactInterval 12 1695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1695 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1695) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1695 : oddCount 1695 12 = 10 ∧ acceleratedOrbit 12 1695 = 24452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1695 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1695) = 3 ^ 10 * m + 24452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1695.1, data_12_1695.2]

/-- Complete interval computation for depth 12, residue 1696. -/
theorem bounds_12_1696 : exactInterval 12 1696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1696 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1696) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1696 : oddCount 1696 12 = 2 ∧ acceleratedOrbit 12 1696 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1696 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1696) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1696.1, data_12_1696.2]

/-- Complete interval computation for depth 12, residue 1697. -/
theorem bounds_12_1697 : exactInterval 12 1697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1697 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1697) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1697 : oddCount 1697 12 = 7 ∧ acceleratedOrbit 12 1697 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1697 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1697) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1697.1, data_12_1697.2]

/-- Complete interval computation for depth 12, residue 1698. -/
theorem bounds_12_1698 : exactInterval 12 1698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1698 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1698) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1698 : oddCount 1698 12 = 7 ∧ acceleratedOrbit 12 1698 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1698 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1698) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1698.1, data_12_1698.2]

/-- Complete interval computation for depth 12, residue 1699. -/
theorem bounds_12_1699 : exactInterval 12 1699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1699 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1699) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1699 : oddCount 1699 12 = 7 ∧ acceleratedOrbit 12 1699 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1699 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1699) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1699.1, data_12_1699.2]

/-- Complete interval computation for depth 12, residue 1700. -/
theorem bounds_12_1700 : exactInterval 12 1700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1700 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1700) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1700 : oddCount 1700 12 = 7 ∧ acceleratedOrbit 12 1700 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1700 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1700) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1700.1, data_12_1700.2]

/-- Complete interval computation for depth 12, residue 1701. -/
theorem bounds_12_1701 : exactInterval 12 1701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1701 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1701) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1701 : oddCount 1701 12 = 7 ∧ acceleratedOrbit 12 1701 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1701 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1701) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1701.1, data_12_1701.2]

/-- Complete interval computation for depth 12, residue 1702. -/
theorem bounds_12_1702 : exactInterval 12 1702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1702 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1702) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1702 : oddCount 1702 12 = 7 ∧ acceleratedOrbit 12 1702 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1702 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1702) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1702.1, data_12_1702.2]

/-- Complete interval computation for depth 12, residue 1703. -/
theorem bounds_12_1703 : exactInterval 12 1703 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1703 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1703) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1703 : oddCount 1703 12 = 7 ∧ acceleratedOrbit 12 1703 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1703 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1703) = 3 ^ 7 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1703.1, data_12_1703.2]

end Collatz.Research.StoppingAtlas.Batch0311
