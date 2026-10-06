import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0177

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1679. -/
theorem bounds_11_1679 : exactInterval 11 1679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1679 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1679) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1679 : oddCount 1679 11 = 7 ∧ acceleratedOrbit 11 1679 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1679 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1679) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1679.1, data_11_1679.2]

/-- Complete interval computation for depth 11, residue 1680. -/
theorem bounds_11_1680 : exactInterval 11 1680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1680 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1680) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1680 : oddCount 1680 11 = 5 ∧ acceleratedOrbit 11 1680 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1680 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1680) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1680.1, data_11_1680.2]

/-- Complete interval computation for depth 11, residue 1681. -/
theorem bounds_11_1681 : exactInterval 11 1681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1681 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1681) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1681 : oddCount 1681 11 = 5 ∧ acceleratedOrbit 11 1681 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1681 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1681) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1681.1, data_11_1681.2]

/-- Complete interval computation for depth 11, residue 1682. -/
theorem bounds_11_1682 : exactInterval 11 1682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1682 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1682) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1682 : oddCount 1682 11 = 5 ∧ acceleratedOrbit 11 1682 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1682 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1682) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1682.1, data_11_1682.2]

/-- Complete interval computation for depth 11, residue 1683. -/
theorem bounds_11_1683 : exactInterval 11 1683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1683 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1683) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1683 : oddCount 1683 11 = 5 ∧ acceleratedOrbit 11 1683 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1683 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1683) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1683.1, data_11_1683.2]

/-- Complete interval computation for depth 11, residue 1684. -/
theorem bounds_11_1684 : exactInterval 11 1684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1684 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1684) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1684 : oddCount 1684 11 = 5 ∧ acceleratedOrbit 11 1684 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1684 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1684) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1684.1, data_11_1684.2]

/-- Complete interval computation for depth 11, residue 1685. -/
theorem bounds_11_1685 : exactInterval 11 1685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1685 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1685) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1685 : oddCount 1685 11 = 5 ∧ acceleratedOrbit 11 1685 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1685 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1685) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1685.1, data_11_1685.2]

/-- Complete interval computation for depth 11, residue 1686. -/
theorem bounds_11_1686 : exactInterval 11 1686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1686 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1686) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1686 : oddCount 1686 11 = 4 ∧ acceleratedOrbit 11 1686 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1686 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1686) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1686.1, data_11_1686.2]

/-- Complete interval computation for depth 11, residue 1687. -/
theorem bounds_11_1687 : exactInterval 11 1687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1687 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1687) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1687 : oddCount 1687 11 = 4 ∧ acceleratedOrbit 11 1687 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1687 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1687) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1687.1, data_11_1687.2]

/-- Complete interval computation for depth 11, residue 1688. -/
theorem bounds_11_1688 : exactInterval 11 1688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1688 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1688) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1688 : oddCount 1688 11 = 5 ∧ acceleratedOrbit 11 1688 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1688 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1688) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1688.1, data_11_1688.2]

/-- Complete interval computation for depth 11, residue 1689. -/
theorem bounds_11_1689 : exactInterval 11 1689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1689 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1689) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1689 : oddCount 1689 11 = 7 ∧ acceleratedOrbit 11 1689 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1689 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1689) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1689.1, data_11_1689.2]

/-- Complete interval computation for depth 11, residue 1690. -/
theorem bounds_11_1690 : exactInterval 11 1690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1690 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1690) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1690 : oddCount 1690 11 = 5 ∧ acceleratedOrbit 11 1690 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1690 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1690) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1690.1, data_11_1690.2]

/-- Complete interval computation for depth 11, residue 1691. -/
theorem bounds_11_1691 : exactInterval 11 1691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1691 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1691) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1691 : oddCount 1691 11 = 8 ∧ acceleratedOrbit 11 1691 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1691 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1691) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1691.1, data_11_1691.2]

/-- Complete interval computation for depth 11, residue 1692. -/
theorem bounds_11_1692 : exactInterval 11 1692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1692 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1692) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1692 : oddCount 1692 11 = 6 ∧ acceleratedOrbit 11 1692 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1692 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1692) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1692.1, data_11_1692.2]

/-- Complete interval computation for depth 11, residue 1693. -/
theorem bounds_11_1693 : exactInterval 11 1693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1693 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1693) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1693 : oddCount 1693 11 = 6 ∧ acceleratedOrbit 11 1693 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1693 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1693) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1693.1, data_11_1693.2]

end Collatz.Research.StoppingAtlas.Batch0177
