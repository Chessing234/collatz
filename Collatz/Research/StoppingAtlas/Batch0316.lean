import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0316

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1766. -/
theorem bounds_12_1766 : exactInterval 12 1766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1766 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1766) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1766 : oddCount 1766 12 = 4 ∧ acceleratedOrbit 12 1766 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1766 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1766) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1766.1, data_12_1766.2]

/-- Complete interval computation for depth 12, residue 1767. -/
theorem bounds_12_1767 : exactInterval 12 1767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1767 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1767) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1767 : oddCount 1767 12 = 9 ∧ acceleratedOrbit 12 1767 = 8498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1767 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1767) = 3 ^ 9 * m + 8498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1767.1, data_12_1767.2]

/-- Complete interval computation for depth 12, residue 1768. -/
theorem bounds_12_1768 : exactInterval 12 1768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1768 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1768) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1768 : oddCount 1768 12 = 5 ∧ acceleratedOrbit 12 1768 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1768 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1768) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1768.1, data_12_1768.2]

/-- Complete interval computation for depth 12, residue 1769. -/
theorem bounds_12_1769 : exactInterval 12 1769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1769 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1769) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1769 : oddCount 1769 12 = 8 ∧ acceleratedOrbit 12 1769 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1769 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1769) = 3 ^ 8 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1769.1, data_12_1769.2]

/-- Complete interval computation for depth 12, residue 1770. -/
theorem bounds_12_1770 : exactInterval 12 1770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1770 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1770) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1770 : oddCount 1770 12 = 5 ∧ acceleratedOrbit 12 1770 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1770 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1770) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1770.1, data_12_1770.2]

/-- Complete interval computation for depth 12, residue 1771. -/
theorem bounds_12_1771 : exactInterval 12 1771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1771 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1771) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1771 : oddCount 1771 12 = 7 ∧ acceleratedOrbit 12 1771 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1771 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1771) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1771.1, data_12_1771.2]

/-- Complete interval computation for depth 12, residue 1772. -/
theorem bounds_12_1772 : exactInterval 12 1772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1772 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1772) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1772 : oddCount 1772 12 = 6 ∧ acceleratedOrbit 12 1772 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1772 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1772) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1772.1, data_12_1772.2]

/-- Complete interval computation for depth 12, residue 1773. -/
theorem bounds_12_1773 : exactInterval 12 1773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1773 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1773) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1773 : oddCount 1773 12 = 6 ∧ acceleratedOrbit 12 1773 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1773 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1773) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1773.1, data_12_1773.2]

/-- Complete interval computation for depth 12, residue 1774. -/
theorem bounds_12_1774 : exactInterval 12 1774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1774 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1774) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1774 : oddCount 1774 12 = 6 ∧ acceleratedOrbit 12 1774 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1774 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1774) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1774.1, data_12_1774.2]

/-- Complete interval computation for depth 12, residue 1775. -/
theorem bounds_12_1775 : exactInterval 12 1775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1775 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1775) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1775 : oddCount 1775 12 = 8 ∧ acceleratedOrbit 12 1775 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1775 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1775) = 3 ^ 8 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1775.1, data_12_1775.2]

/-- Complete interval computation for depth 12, residue 1776. -/
theorem bounds_12_1776 : exactInterval 12 1776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1776 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1776) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1776 : oddCount 1776 12 = 6 ∧ acceleratedOrbit 12 1776 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1776 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1776) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1776.1, data_12_1776.2]

/-- Complete interval computation for depth 12, residue 1777. -/
theorem bounds_12_1777 : exactInterval 12 1777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1777 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1777) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1777 : oddCount 1777 12 = 5 ∧ acceleratedOrbit 12 1777 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1777 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1777) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1777.1, data_12_1777.2]

/-- Complete interval computation for depth 12, residue 1778. -/
theorem bounds_12_1778 : exactInterval 12 1778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1778 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1778) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1778 : oddCount 1778 12 = 8 ∧ acceleratedOrbit 12 1778 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1778 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1778) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1778.1, data_12_1778.2]

/-- Complete interval computation for depth 12, residue 1779. -/
theorem bounds_12_1779 : exactInterval 12 1779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1779 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1779) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1779 : oddCount 1779 12 = 8 ∧ acceleratedOrbit 12 1779 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1779 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1779) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1779.1, data_12_1779.2]

/-- Complete interval computation for depth 12, residue 1780. -/
theorem bounds_12_1780 : exactInterval 12 1780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1780 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1780) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1780 : oddCount 1780 12 = 6 ∧ acceleratedOrbit 12 1780 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1780 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1780) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1780.1, data_12_1780.2]

end Collatz.Research.StoppingAtlas.Batch0316
