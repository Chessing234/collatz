import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0052

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1671. -/
theorem bounds_15_1671 : exactInterval 15 1671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1671 : oddCount 1671 15 = 7 ∧ acceleratedOrbit 15 1671 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1671) = 3 ^ 7 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1671.1, data_15_1671.2]

/-- Complete interval computation for depth 15, residue 1672. -/
theorem bounds_15_1672 : exactInterval 15 1672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1672 : oddCount 1672 15 = 6 ∧ acceleratedOrbit 15 1672 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1672) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1672.1, data_15_1672.2]

/-- Complete interval computation for depth 15, residue 1673. -/
theorem bounds_15_1673 : exactInterval 15 1673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1673 : oddCount 1673 15 = 10 ∧ acceleratedOrbit 15 1673 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1673) = 3 ^ 10 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1673.1, data_15_1673.2]

/-- Complete interval computation for depth 15, residue 1674. -/
theorem bounds_15_1674 : exactInterval 15 1674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1674 : oddCount 1674 15 = 6 ∧ acceleratedOrbit 15 1674 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1674) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1674.1, data_15_1674.2]

/-- Complete interval computation for depth 15, residue 1675. -/
theorem bounds_15_1675 : exactInterval 15 1675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1675 : oddCount 1675 15 = 8 ∧ acceleratedOrbit 15 1675 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1675) = 3 ^ 8 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1675.1, data_15_1675.2]

/-- Complete interval computation for depth 15, residue 1676. -/
theorem bounds_15_1676 : exactInterval 15 1676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1676 : oddCount 1676 15 = 6 ∧ acceleratedOrbit 15 1676 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1676) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1676.1, data_15_1676.2]

/-- Complete interval computation for depth 15, residue 1677. -/
theorem bounds_15_1677 : exactInterval 15 1677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1677 : oddCount 1677 15 = 6 ∧ acceleratedOrbit 15 1677 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1677) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1677.1, data_15_1677.2]

/-- Complete interval computation for depth 15, residue 1678. -/
theorem bounds_15_1678 : exactInterval 15 1678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1678 : oddCount 1678 15 = 9 ∧ acceleratedOrbit 15 1678 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1678) = 3 ^ 9 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1678.1, data_15_1678.2]

/-- Complete interval computation for depth 15, residue 1679. -/
theorem bounds_15_1679 : exactInterval 15 1679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1679 : oddCount 1679 15 = 9 ∧ acceleratedOrbit 15 1679 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1679) = 3 ^ 9 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1679.1, data_15_1679.2]

/-- Complete interval computation for depth 15, residue 1680. -/
theorem bounds_15_1680 : exactInterval 15 1680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1680 : oddCount 1680 15 = 6 ∧ acceleratedOrbit 15 1680 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1680) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1680.1, data_15_1680.2]

/-- Complete interval computation for depth 15, residue 1681. -/
theorem bounds_15_1681 : exactInterval 15 1681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1681 : oddCount 1681 15 = 6 ∧ acceleratedOrbit 15 1681 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1681) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1681.1, data_15_1681.2]

/-- Complete interval computation for depth 15, residue 1682. -/
theorem bounds_15_1682 : exactInterval 15 1682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1682 : oddCount 1682 15 = 6 ∧ acceleratedOrbit 15 1682 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1682) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1682.1, data_15_1682.2]

/-- Complete interval computation for depth 15, residue 1683. -/
theorem bounds_15_1683 : exactInterval 15 1683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1683 : oddCount 1683 15 = 6 ∧ acceleratedOrbit 15 1683 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1683) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1683.1, data_15_1683.2]

/-- Complete interval computation for depth 15, residue 1684. -/
theorem bounds_15_1684 : exactInterval 15 1684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1684 : oddCount 1684 15 = 6 ∧ acceleratedOrbit 15 1684 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1684) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1684.1, data_15_1684.2]

/-- Complete interval computation for depth 15, residue 1685. -/
theorem bounds_15_1685 : exactInterval 15 1685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1685 : oddCount 1685 15 = 6 ∧ acceleratedOrbit 15 1685 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1685) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1685.1, data_15_1685.2]

/-- Complete interval computation for depth 15, residue 1686. -/
theorem bounds_15_1686 : exactInterval 15 1686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1686 : oddCount 1686 15 = 6 ∧ acceleratedOrbit 15 1686 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1686) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1686.1, data_15_1686.2]

/-- Complete interval computation for depth 15, residue 1687. -/
theorem bounds_15_1687 : exactInterval 15 1687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1687 : oddCount 1687 15 = 6 ∧ acceleratedOrbit 15 1687 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1687) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1687.1, data_15_1687.2]

/-- Complete interval computation for depth 15, residue 1688. -/
theorem bounds_15_1688 : exactInterval 15 1688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1688 : oddCount 1688 15 = 6 ∧ acceleratedOrbit 15 1688 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1688) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1688.1, data_15_1688.2]

/-- Complete interval computation for depth 15, residue 1689. -/
theorem bounds_15_1689 : exactInterval 15 1689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1689 : oddCount 1689 15 = 7 ∧ acceleratedOrbit 15 1689 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1689) = 3 ^ 7 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1689.1, data_15_1689.2]

/-- Complete interval computation for depth 15, residue 1690. -/
theorem bounds_15_1690 : exactInterval 15 1690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1690 : oddCount 1690 15 = 6 ∧ acceleratedOrbit 15 1690 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1690) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1690.1, data_15_1690.2]

/-- Complete interval computation for depth 15, residue 1691. -/
theorem bounds_15_1691 : exactInterval 15 1691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1691 : oddCount 1691 15 = 11 ∧ acceleratedOrbit 15 1691 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1691) = 3 ^ 11 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1691.1, data_15_1691.2]

/-- Complete interval computation for depth 15, residue 1692. -/
theorem bounds_15_1692 : exactInterval 15 1692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1692 : oddCount 1692 15 = 8 ∧ acceleratedOrbit 15 1692 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1692) = 3 ^ 8 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1692.1, data_15_1692.2]

/-- Complete interval computation for depth 15, residue 1693. -/
theorem bounds_15_1693 : exactInterval 15 1693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1693 : oddCount 1693 15 = 8 ∧ acceleratedOrbit 15 1693 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1693) = 3 ^ 8 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1693.1, data_15_1693.2]

/-- Complete interval computation for depth 15, residue 1694. -/
theorem bounds_15_1694 : exactInterval 15 1694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1694 : oddCount 1694 15 = 8 ∧ acceleratedOrbit 15 1694 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1694) = 3 ^ 8 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1694.1, data_15_1694.2]

/-- Complete interval computation for depth 15, residue 1695. -/
theorem bounds_15_1695 : exactInterval 15 1695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1695 : oddCount 1695 15 = 11 ∧ acceleratedOrbit 15 1695 = 9170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1695) = 3 ^ 11 * m + 9170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1695.1, data_15_1695.2]

/-- Complete interval computation for depth 15, residue 1696. -/
theorem bounds_15_1696 : exactInterval 15 1696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1696 : oddCount 1696 15 = 3 ∧ acceleratedOrbit 15 1696 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1696) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1696.1, data_15_1696.2]

/-- Complete interval computation for depth 15, residue 1697. -/
theorem bounds_15_1697 : exactInterval 15 1697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1697 : oddCount 1697 15 = 8 ∧ acceleratedOrbit 15 1697 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1697) = 3 ^ 8 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1697.1, data_15_1697.2]

/-- Complete interval computation for depth 15, residue 1698. -/
theorem bounds_15_1698 : exactInterval 15 1698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1698 : oddCount 1698 15 = 10 ∧ acceleratedOrbit 15 1698 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1698) = 3 ^ 10 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1698.1, data_15_1698.2]

/-- Complete interval computation for depth 15, residue 1699. -/
theorem bounds_15_1699 : exactInterval 15 1699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1699 : oddCount 1699 15 = 10 ∧ acceleratedOrbit 15 1699 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1699) = 3 ^ 10 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1699.1, data_15_1699.2]

/-- Complete interval computation for depth 15, residue 1700. -/
theorem bounds_15_1700 : exactInterval 15 1700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1700 : oddCount 1700 15 = 10 ∧ acceleratedOrbit 15 1700 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1700) = 3 ^ 10 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1700.1, data_15_1700.2]

/-- Complete interval computation for depth 15, residue 1701. -/
theorem bounds_15_1701 : exactInterval 15 1701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1701 : oddCount 1701 15 = 10 ∧ acceleratedOrbit 15 1701 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1701) = 3 ^ 10 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1701.1, data_15_1701.2]

/-- Complete interval computation for depth 15, residue 1702. -/
theorem bounds_15_1702 : exactInterval 15 1702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1702 : oddCount 1702 15 = 10 ∧ acceleratedOrbit 15 1702 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1702) = 3 ^ 10 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1702.1, data_15_1702.2]

end Collatz.Research.PassageAtlas.Batch0052
