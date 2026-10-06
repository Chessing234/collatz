import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0577

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1679. -/
theorem bounds_13_1679 : exactInterval 13 1679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1679 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1679) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1679 : oddCount 1679 13 = 9 ∧ acceleratedOrbit 13 1679 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1679 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1679) = 3 ^ 9 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1679.1, data_13_1679.2]

/-- Complete interval computation for depth 13, residue 1680. -/
theorem bounds_13_1680 : exactInterval 13 1680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1680 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1680) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1680 : oddCount 1680 13 = 6 ∧ acceleratedOrbit 13 1680 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1680 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1680) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1680.1, data_13_1680.2]

/-- Complete interval computation for depth 13, residue 1681. -/
theorem bounds_13_1681 : exactInterval 13 1681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1681 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1681) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1681 : oddCount 1681 13 = 5 ∧ acceleratedOrbit 13 1681 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1681 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1681) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1681.1, data_13_1681.2]

/-- Complete interval computation for depth 13, residue 1682. -/
theorem bounds_13_1682 : exactInterval 13 1682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1682 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1682) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1682 : oddCount 1682 13 = 5 ∧ acceleratedOrbit 13 1682 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1682 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1682) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1682.1, data_13_1682.2]

/-- Complete interval computation for depth 13, residue 1683. -/
theorem bounds_13_1683 : exactInterval 13 1683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1683 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1683) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1683 : oddCount 1683 13 = 5 ∧ acceleratedOrbit 13 1683 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1683 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1683) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1683.1, data_13_1683.2]

/-- Complete interval computation for depth 13, residue 1684. -/
theorem bounds_13_1684 : exactInterval 13 1684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1684 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1684) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1684 : oddCount 1684 13 = 6 ∧ acceleratedOrbit 13 1684 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1684 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1684) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1684.1, data_13_1684.2]

/-- Complete interval computation for depth 13, residue 1685. -/
theorem bounds_13_1685 : exactInterval 13 1685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1685 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1685) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1685 : oddCount 1685 13 = 6 ∧ acceleratedOrbit 13 1685 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1685 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1685) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1685.1, data_13_1685.2]

/-- Complete interval computation for depth 13, residue 1686. -/
theorem bounds_13_1686 : exactInterval 13 1686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1686 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1686) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1686 : oddCount 1686 13 = 6 ∧ acceleratedOrbit 13 1686 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1686 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1686) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1686.1, data_13_1686.2]

/-- Complete interval computation for depth 13, residue 1687. -/
theorem bounds_13_1687 : exactInterval 13 1687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1687 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1687) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1687 : oddCount 1687 13 = 6 ∧ acceleratedOrbit 13 1687 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1687 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1687) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1687.1, data_13_1687.2]

/-- Complete interval computation for depth 13, residue 1688. -/
theorem bounds_13_1688 : exactInterval 13 1688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1688 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1688) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1688 : oddCount 1688 13 = 6 ∧ acceleratedOrbit 13 1688 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1688 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1688) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1688.1, data_13_1688.2]

/-- Complete interval computation for depth 13, residue 1689. -/
theorem bounds_13_1689 : exactInterval 13 1689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1689 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1689) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1689 : oddCount 1689 13 = 7 ∧ acceleratedOrbit 13 1689 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1689 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1689) = 3 ^ 7 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1689.1, data_13_1689.2]

/-- Complete interval computation for depth 13, residue 1690. -/
theorem bounds_13_1690 : exactInterval 13 1690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1690 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1690) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1690 : oddCount 1690 13 = 6 ∧ acceleratedOrbit 13 1690 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1690 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1690) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1690.1, data_13_1690.2]

/-- Complete interval computation for depth 13, residue 1691. -/
theorem bounds_13_1691 : exactInterval 13 1691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1691 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1691) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1691 : oddCount 1691 13 = 9 ∧ acceleratedOrbit 13 1691 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1691 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1691) = 3 ^ 9 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1691.1, data_13_1691.2]

/-- Complete interval computation for depth 13, residue 1692. -/
theorem bounds_13_1692 : exactInterval 13 1692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1692 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1692) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1692 : oddCount 1692 13 = 6 ∧ acceleratedOrbit 13 1692 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1692 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1692) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1692.1, data_13_1692.2]

/-- Complete interval computation for depth 13, residue 1693. -/
theorem bounds_13_1693 : exactInterval 13 1693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1693 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1693) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1693 : oddCount 1693 13 = 6 ∧ acceleratedOrbit 13 1693 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1693 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1693) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1693.1, data_13_1693.2]

end Collatz.Research.StoppingAtlas.Batch0577
