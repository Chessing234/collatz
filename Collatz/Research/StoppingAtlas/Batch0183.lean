import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0183

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1771. -/
theorem bounds_11_1771 : exactInterval 11 1771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1771 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1771) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1771 : oddCount 1771 11 = 6 ∧ acceleratedOrbit 11 1771 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1771 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1771) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1771.1, data_11_1771.2]

/-- Complete interval computation for depth 11, residue 1772. -/
theorem bounds_11_1772 : exactInterval 11 1772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1772 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1772) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1772 : oddCount 1772 11 = 5 ∧ acceleratedOrbit 11 1772 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1772 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1772) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1772.1, data_11_1772.2]

/-- Complete interval computation for depth 11, residue 1773. -/
theorem bounds_11_1773 : exactInterval 11 1773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1773 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1773) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1773 : oddCount 1773 11 = 5 ∧ acceleratedOrbit 11 1773 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1773 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1773) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1773.1, data_11_1773.2]

/-- Complete interval computation for depth 11, residue 1774. -/
theorem bounds_11_1774 : exactInterval 11 1774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1774 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1774) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1774 : oddCount 1774 11 = 5 ∧ acceleratedOrbit 11 1774 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1774 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1774) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1774.1, data_11_1774.2]

/-- Complete interval computation for depth 11, residue 1775. -/
theorem bounds_11_1775 : exactInterval 11 1775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1775 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1775) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1775 : oddCount 1775 11 = 8 ∧ acceleratedOrbit 11 1775 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1775 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1775) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1775.1, data_11_1775.2]

/-- Complete interval computation for depth 11, residue 1776. -/
theorem bounds_11_1776 : exactInterval 11 1776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1776 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1776) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1776 : oddCount 1776 11 = 6 ∧ acceleratedOrbit 11 1776 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1776 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1776) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1776.1, data_11_1776.2]

/-- Complete interval computation for depth 11, residue 1777. -/
theorem bounds_11_1777 : exactInterval 11 1777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1777 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1777) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1777 : oddCount 1777 11 = 4 ∧ acceleratedOrbit 11 1777 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1777 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1777) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1777.1, data_11_1777.2]

/-- Complete interval computation for depth 11, residue 1778. -/
theorem bounds_11_1778 : exactInterval 11 1778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1778 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1778) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1778 : oddCount 1778 11 = 7 ∧ acceleratedOrbit 11 1778 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1778 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1778) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1778.1, data_11_1778.2]

/-- Complete interval computation for depth 11, residue 1779. -/
theorem bounds_11_1779 : exactInterval 11 1779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1779 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1779) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1779 : oddCount 1779 11 = 7 ∧ acceleratedOrbit 11 1779 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1779 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1779) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1779.1, data_11_1779.2]

/-- Complete interval computation for depth 11, residue 1780. -/
theorem bounds_11_1780 : exactInterval 11 1780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1780 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1780) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1780 : oddCount 1780 11 = 6 ∧ acceleratedOrbit 11 1780 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1780 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1780) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1780.1, data_11_1780.2]

/-- Complete interval computation for depth 11, residue 1781. -/
theorem bounds_11_1781 : exactInterval 11 1781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1781 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1781) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1781 : oddCount 1781 11 = 6 ∧ acceleratedOrbit 11 1781 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1781 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1781) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1781.1, data_11_1781.2]

/-- Complete interval computation for depth 11, residue 1782. -/
theorem bounds_11_1782 : exactInterval 11 1782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1782 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1782) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1782 : oddCount 1782 11 = 7 ∧ acceleratedOrbit 11 1782 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1782 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1782) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1782.1, data_11_1782.2]

/-- Complete interval computation for depth 11, residue 1783. -/
theorem bounds_11_1783 : exactInterval 11 1783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1783 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1783) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1783 : oddCount 1783 11 = 7 ∧ acceleratedOrbit 11 1783 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1783 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1783) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1783.1, data_11_1783.2]

/-- Complete interval computation for depth 11, residue 1784. -/
theorem bounds_11_1784 : exactInterval 11 1784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1784 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1784) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1784 : oddCount 1784 11 = 6 ∧ acceleratedOrbit 11 1784 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1784 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1784) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1784.1, data_11_1784.2]

/-- Complete interval computation for depth 11, residue 1785. -/
theorem bounds_11_1785 : exactInterval 11 1785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1785 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1785) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1785 : oddCount 1785 11 = 5 ∧ acceleratedOrbit 11 1785 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1785 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1785) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1785.1, data_11_1785.2]

end Collatz.Research.StoppingAtlas.Batch0183
