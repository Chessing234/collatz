import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0583

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1771. -/
theorem bounds_13_1771 : exactInterval 13 1771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1771 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1771) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1771 : oddCount 1771 13 = 8 ∧ acceleratedOrbit 13 1771 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1771 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1771) = 3 ^ 8 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1771.1, data_13_1771.2]

/-- Complete interval computation for depth 13, residue 1772. -/
theorem bounds_13_1772 : exactInterval 13 1772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1772 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1772) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1772 : oddCount 1772 13 = 7 ∧ acceleratedOrbit 13 1772 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1772 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1772) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1772.1, data_13_1772.2]

/-- Complete interval computation for depth 13, residue 1773. -/
theorem bounds_13_1773 : exactInterval 13 1773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1773 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1773) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1773 : oddCount 1773 13 = 7 ∧ acceleratedOrbit 13 1773 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1773 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1773) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1773.1, data_13_1773.2]

/-- Complete interval computation for depth 13, residue 1774. -/
theorem bounds_13_1774 : exactInterval 13 1774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1774 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1774) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1774 : oddCount 1774 13 = 7 ∧ acceleratedOrbit 13 1774 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1774 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1774) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1774.1, data_13_1774.2]

/-- Complete interval computation for depth 13, residue 1775. -/
theorem bounds_13_1775 : exactInterval 13 1775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1775 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1775) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1775 : oddCount 1775 13 = 9 ∧ acceleratedOrbit 13 1775 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1775 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1775) = 3 ^ 9 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1775.1, data_13_1775.2]

/-- Complete interval computation for depth 13, residue 1776. -/
theorem bounds_13_1776 : exactInterval 13 1776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1776 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1776) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1776 : oddCount 1776 13 = 7 ∧ acceleratedOrbit 13 1776 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1776 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1776) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1776.1, data_13_1776.2]

/-- Complete interval computation for depth 13, residue 1777. -/
theorem bounds_13_1777 : exactInterval 13 1777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1777 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1777) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1777 : oddCount 1777 13 = 6 ∧ acceleratedOrbit 13 1777 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1777 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1777) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1777.1, data_13_1777.2]

/-- Complete interval computation for depth 13, residue 1778. -/
theorem bounds_13_1778 : exactInterval 13 1778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1778 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1778) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1778 : oddCount 1778 13 = 9 ∧ acceleratedOrbit 13 1778 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1778 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1778) = 3 ^ 9 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1778.1, data_13_1778.2]

/-- Complete interval computation for depth 13, residue 1779. -/
theorem bounds_13_1779 : exactInterval 13 1779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1779 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1779) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1779 : oddCount 1779 13 = 9 ∧ acceleratedOrbit 13 1779 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1779 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1779) = 3 ^ 9 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1779.1, data_13_1779.2]

/-- Complete interval computation for depth 13, residue 1780. -/
theorem bounds_13_1780 : exactInterval 13 1780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1780 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1780) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1780 : oddCount 1780 13 = 7 ∧ acceleratedOrbit 13 1780 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1780 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1780) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1780.1, data_13_1780.2]

/-- Complete interval computation for depth 13, residue 1781. -/
theorem bounds_13_1781 : exactInterval 13 1781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1781 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1781) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1781 : oddCount 1781 13 = 7 ∧ acceleratedOrbit 13 1781 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1781 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1781) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1781.1, data_13_1781.2]

/-- Complete interval computation for depth 13, residue 1782. -/
theorem bounds_13_1782 : exactInterval 13 1782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1782 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1782) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1782 : oddCount 1782 13 = 9 ∧ acceleratedOrbit 13 1782 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1782 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1782) = 3 ^ 9 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1782.1, data_13_1782.2]

/-- Complete interval computation for depth 13, residue 1783. -/
theorem bounds_13_1783 : exactInterval 13 1783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1783 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1783) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1783 : oddCount 1783 13 = 9 ∧ acceleratedOrbit 13 1783 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1783 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1783) = 3 ^ 9 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1783.1, data_13_1783.2]

/-- Complete interval computation for depth 13, residue 1784. -/
theorem bounds_13_1784 : exactInterval 13 1784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1784 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1784) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1784 : oddCount 1784 13 = 7 ∧ acceleratedOrbit 13 1784 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1784 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1784) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1784.1, data_13_1784.2]

/-- Complete interval computation for depth 13, residue 1785. -/
theorem bounds_13_1785 : exactInterval 13 1785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1785 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1785) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1785 : oddCount 1785 13 = 5 ∧ acceleratedOrbit 13 1785 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1785 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1785) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1785.1, data_13_1785.2]

end Collatz.Research.StoppingAtlas.Batch0583
