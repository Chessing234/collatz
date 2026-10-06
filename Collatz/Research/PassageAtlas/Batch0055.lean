import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0055

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1769. -/
theorem bounds_15_1769 : exactInterval 15 1769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1769 : oddCount 1769 15 = 9 ∧ acceleratedOrbit 15 1769 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1769) = 3 ^ 9 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1769.1, data_15_1769.2]

/-- Complete interval computation for depth 15, residue 1770. -/
theorem bounds_15_1770 : exactInterval 15 1770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1770 : oddCount 1770 15 = 7 ∧ acceleratedOrbit 15 1770 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1770) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1770.1, data_15_1770.2]

/-- Complete interval computation for depth 15, residue 1771. -/
theorem bounds_15_1771 : exactInterval 15 1771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1771 : oddCount 1771 15 = 9 ∧ acceleratedOrbit 15 1771 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1771) = 3 ^ 9 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1771.1, data_15_1771.2]

/-- Complete interval computation for depth 15, residue 1772. -/
theorem bounds_15_1772 : exactInterval 15 1772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1772 : oddCount 1772 15 = 7 ∧ acceleratedOrbit 15 1772 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1772) = 3 ^ 7 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1772.1, data_15_1772.2]

/-- Complete interval computation for depth 15, residue 1773. -/
theorem bounds_15_1773 : exactInterval 15 1773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1773 : oddCount 1773 15 = 7 ∧ acceleratedOrbit 15 1773 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1773) = 3 ^ 7 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1773.1, data_15_1773.2]

/-- Complete interval computation for depth 15, residue 1774. -/
theorem bounds_15_1774 : exactInterval 15 1774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1774 : oddCount 1774 15 = 7 ∧ acceleratedOrbit 15 1774 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1774) = 3 ^ 7 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1774.1, data_15_1774.2]

/-- Complete interval computation for depth 15, residue 1775. -/
theorem bounds_15_1775 : exactInterval 15 1775 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1775) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1775 : oddCount 1775 15 = 9 ∧ acceleratedOrbit 15 1775 = 1067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1775) = 3 ^ 9 * m + 1067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1775.1, data_15_1775.2]

/-- Complete interval computation for depth 15, residue 1776. -/
theorem bounds_15_1776 : exactInterval 15 1776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1776 : oddCount 1776 15 = 9 ∧ acceleratedOrbit 15 1776 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1776) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1776.1, data_15_1776.2]

/-- Complete interval computation for depth 15, residue 1777. -/
theorem bounds_15_1777 : exactInterval 15 1777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1777 : oddCount 1777 15 = 7 ∧ acceleratedOrbit 15 1777 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1777) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1777.1, data_15_1777.2]

/-- Complete interval computation for depth 15, residue 1778. -/
theorem bounds_15_1778 : exactInterval 15 1778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1778 : oddCount 1778 15 = 11 ∧ acceleratedOrbit 15 1778 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1778) = 3 ^ 11 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1778.1, data_15_1778.2]

/-- Complete interval computation for depth 15, residue 1779. -/
theorem bounds_15_1779 : exactInterval 15 1779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1779 : oddCount 1779 15 = 11 ∧ acceleratedOrbit 15 1779 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1779) = 3 ^ 11 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1779.1, data_15_1779.2]

/-- Complete interval computation for depth 15, residue 1780. -/
theorem bounds_15_1780 : exactInterval 15 1780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1780 : oddCount 1780 15 = 9 ∧ acceleratedOrbit 15 1780 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1780) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1780.1, data_15_1780.2]

/-- Complete interval computation for depth 15, residue 1781. -/
theorem bounds_15_1781 : exactInterval 15 1781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1781 : oddCount 1781 15 = 9 ∧ acceleratedOrbit 15 1781 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1781) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1781.1, data_15_1781.2]

/-- Complete interval computation for depth 15, residue 1782. -/
theorem bounds_15_1782 : exactInterval 15 1782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1782 : oddCount 1782 15 = 9 ∧ acceleratedOrbit 15 1782 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1782) = 3 ^ 9 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1782.1, data_15_1782.2]

/-- Complete interval computation for depth 15, residue 1783. -/
theorem bounds_15_1783 : exactInterval 15 1783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1783 : oddCount 1783 15 = 9 ∧ acceleratedOrbit 15 1783 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1783) = 3 ^ 9 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1783.1, data_15_1783.2]

/-- Complete interval computation for depth 15, residue 1784. -/
theorem bounds_15_1784 : exactInterval 15 1784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1784 : oddCount 1784 15 = 9 ∧ acceleratedOrbit 15 1784 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1784) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1784.1, data_15_1784.2]

/-- Complete interval computation for depth 15, residue 1785. -/
theorem bounds_15_1785 : exactInterval 15 1785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1785 : oddCount 1785 15 = 6 ∧ acceleratedOrbit 15 1785 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1785) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1785.1, data_15_1785.2]

/-- Complete interval computation for depth 15, residue 1786. -/
theorem bounds_15_1786 : exactInterval 15 1786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1786 : oddCount 1786 15 = 9 ∧ acceleratedOrbit 15 1786 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1786) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1786.1, data_15_1786.2]

/-- Complete interval computation for depth 15, residue 1787. -/
theorem bounds_15_1787 : exactInterval 15 1787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1787 : oddCount 1787 15 = 9 ∧ acceleratedOrbit 15 1787 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1787) = 3 ^ 9 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1787.1, data_15_1787.2]

/-- Complete interval computation for depth 15, residue 1788. -/
theorem bounds_15_1788 : exactInterval 15 1788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1788 : oddCount 1788 15 = 10 ∧ acceleratedOrbit 15 1788 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1788) = 3 ^ 10 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1788.1, data_15_1788.2]

/-- Complete interval computation for depth 15, residue 1789. -/
theorem bounds_15_1789 : exactInterval 15 1789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1789 : oddCount 1789 15 = 10 ∧ acceleratedOrbit 15 1789 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1789) = 3 ^ 10 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1789.1, data_15_1789.2]

/-- Complete interval computation for depth 15, residue 1790. -/
theorem bounds_15_1790 : exactInterval 15 1790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1790 : oddCount 1790 15 = 10 ∧ acceleratedOrbit 15 1790 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1790) = 3 ^ 10 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1790.1, data_15_1790.2]

/-- Complete interval computation for depth 15, residue 1791. -/
theorem bounds_15_1791 : exactInterval 15 1791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1791 : oddCount 1791 15 = 11 ∧ acceleratedOrbit 15 1791 = 9688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1791) = 3 ^ 11 * m + 9688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1791.1, data_15_1791.2]

/-- Complete interval computation for depth 15, residue 1792. -/
theorem bounds_15_1792 : exactInterval 15 1792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1792 : oddCount 1792 15 = 4 ∧ acceleratedOrbit 15 1792 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1792) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1792.1, data_15_1792.2]

/-- Complete interval computation for depth 15, residue 1793. -/
theorem bounds_15_1793 : exactInterval 15 1793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1793 : oddCount 1793 15 = 7 ∧ acceleratedOrbit 15 1793 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1793) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1793.1, data_15_1793.2]

/-- Complete interval computation for depth 15, residue 1794. -/
theorem bounds_15_1794 : exactInterval 15 1794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1794 : oddCount 1794 15 = 8 ∧ acceleratedOrbit 15 1794 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1794) = 3 ^ 8 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1794.1, data_15_1794.2]

/-- Complete interval computation for depth 15, residue 1795. -/
theorem bounds_15_1795 : exactInterval 15 1795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1795 : oddCount 1795 15 = 8 ∧ acceleratedOrbit 15 1795 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1795) = 3 ^ 8 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1795.1, data_15_1795.2]

/-- Complete interval computation for depth 15, residue 1796. -/
theorem bounds_15_1796 : exactInterval 15 1796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1796 : oddCount 1796 15 = 8 ∧ acceleratedOrbit 15 1796 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1796) = 3 ^ 8 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1796.1, data_15_1796.2]

/-- Complete interval computation for depth 15, residue 1797. -/
theorem bounds_15_1797 : exactInterval 15 1797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1797 : oddCount 1797 15 = 8 ∧ acceleratedOrbit 15 1797 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1797) = 3 ^ 8 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1797.1, data_15_1797.2]

/-- Complete interval computation for depth 15, residue 1798. -/
theorem bounds_15_1798 : exactInterval 15 1798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1798 : oddCount 1798 15 = 8 ∧ acceleratedOrbit 15 1798 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1798) = 3 ^ 8 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1798.1, data_15_1798.2]

/-- Complete interval computation for depth 15, residue 1799. -/
theorem bounds_15_1799 : exactInterval 15 1799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1799 : oddCount 1799 15 = 8 ∧ acceleratedOrbit 15 1799 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1799) = 3 ^ 8 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1799.1, data_15_1799.2]

/-- Complete interval computation for depth 15, residue 1800. -/
theorem bounds_15_1800 : exactInterval 15 1800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1800 : oddCount 1800 15 = 9 ∧ acceleratedOrbit 15 1800 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1800) = 3 ^ 9 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1800.1, data_15_1800.2]

/-- Complete interval computation for depth 15, residue 1801. -/
theorem bounds_15_1801 : exactInterval 15 1801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1801 : oddCount 1801 15 = 10 ∧ acceleratedOrbit 15 1801 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1801) = 3 ^ 10 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1801.1, data_15_1801.2]

end Collatz.Research.PassageAtlas.Batch0055
