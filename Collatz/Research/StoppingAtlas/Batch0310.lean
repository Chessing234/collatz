import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0310

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1674. -/
theorem bounds_12_1674 : exactInterval 12 1674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1674 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1674) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1674 : oddCount 1674 12 = 5 ∧ acceleratedOrbit 12 1674 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1674 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1674) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1674.1, data_12_1674.2]

/-- Complete interval computation for depth 12, residue 1675. -/
theorem bounds_12_1675 : exactInterval 12 1675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1675 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1675) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1675 : oddCount 1675 12 = 6 ∧ acceleratedOrbit 12 1675 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1675 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1675) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1675.1, data_12_1675.2]

/-- Complete interval computation for depth 12, residue 1676. -/
theorem bounds_12_1676 : exactInterval 12 1676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1676 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1676) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1676 : oddCount 1676 12 = 5 ∧ acceleratedOrbit 12 1676 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1676 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1676) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1676.1, data_12_1676.2]

/-- Complete interval computation for depth 12, residue 1677. -/
theorem bounds_12_1677 : exactInterval 12 1677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1677 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1677) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1677 : oddCount 1677 12 = 5 ∧ acceleratedOrbit 12 1677 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1677 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1677) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1677.1, data_12_1677.2]

/-- Complete interval computation for depth 12, residue 1678. -/
theorem bounds_12_1678 : exactInterval 12 1678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1678 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1678) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1678 : oddCount 1678 12 = 8 ∧ acceleratedOrbit 12 1678 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1678 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1678) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1678.1, data_12_1678.2]

/-- Complete interval computation for depth 12, residue 1679. -/
theorem bounds_12_1679 : exactInterval 12 1679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1679 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1679) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1679 : oddCount 1679 12 = 8 ∧ acceleratedOrbit 12 1679 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1679 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1679) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1679.1, data_12_1679.2]

/-- Complete interval computation for depth 12, residue 1680. -/
theorem bounds_12_1680 : exactInterval 12 1680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1680 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1680) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1680 : oddCount 1680 12 = 5 ∧ acceleratedOrbit 12 1680 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1680 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1680) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1680.1, data_12_1680.2]

/-- Complete interval computation for depth 12, residue 1681. -/
theorem bounds_12_1681 : exactInterval 12 1681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1681 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1681) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1681 : oddCount 1681 12 = 5 ∧ acceleratedOrbit 12 1681 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1681 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1681) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1681.1, data_12_1681.2]

/-- Complete interval computation for depth 12, residue 1682. -/
theorem bounds_12_1682 : exactInterval 12 1682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1682 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1682) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1682 : oddCount 1682 12 = 5 ∧ acceleratedOrbit 12 1682 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1682 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1682) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1682.1, data_12_1682.2]

/-- Complete interval computation for depth 12, residue 1683. -/
theorem bounds_12_1683 : exactInterval 12 1683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1683 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1683) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1683 : oddCount 1683 12 = 5 ∧ acceleratedOrbit 12 1683 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1683 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1683) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1683.1, data_12_1683.2]

/-- Complete interval computation for depth 12, residue 1684. -/
theorem bounds_12_1684 : exactInterval 12 1684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1684 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1684) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1684 : oddCount 1684 12 = 5 ∧ acceleratedOrbit 12 1684 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1684 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1684) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1684.1, data_12_1684.2]

/-- Complete interval computation for depth 12, residue 1685. -/
theorem bounds_12_1685 : exactInterval 12 1685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1685 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1685) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1685 : oddCount 1685 12 = 5 ∧ acceleratedOrbit 12 1685 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1685 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1685) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1685.1, data_12_1685.2]

/-- Complete interval computation for depth 12, residue 1686. -/
theorem bounds_12_1686 : exactInterval 12 1686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1686 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1686) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1686 : oddCount 1686 12 = 5 ∧ acceleratedOrbit 12 1686 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1686 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1686) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1686.1, data_12_1686.2]

/-- Complete interval computation for depth 12, residue 1687. -/
theorem bounds_12_1687 : exactInterval 12 1687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1687 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1687) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1687 : oddCount 1687 12 = 5 ∧ acceleratedOrbit 12 1687 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1687 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1687) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1687.1, data_12_1687.2]

/-- Complete interval computation for depth 12, residue 1688. -/
theorem bounds_12_1688 : exactInterval 12 1688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1688 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1688) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1688 : oddCount 1688 12 = 5 ∧ acceleratedOrbit 12 1688 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1688 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1688) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1688.1, data_12_1688.2]

end Collatz.Research.StoppingAtlas.Batch0310
