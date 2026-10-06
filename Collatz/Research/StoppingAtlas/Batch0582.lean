import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0582

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1756. -/
theorem bounds_13_1756 : exactInterval 13 1756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1756 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1756) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1756 : oddCount 1756 13 = 6 ∧ acceleratedOrbit 13 1756 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1756 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1756) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1756.1, data_13_1756.2]

/-- Complete interval computation for depth 13, residue 1757. -/
theorem bounds_13_1757 : exactInterval 13 1757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1757 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1757) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1757 : oddCount 1757 13 = 6 ∧ acceleratedOrbit 13 1757 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1757 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1757) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1757.1, data_13_1757.2]

/-- Complete interval computation for depth 13, residue 1758. -/
theorem bounds_13_1758 : exactInterval 13 1758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1758 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1758) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1758 : oddCount 1758 13 = 7 ∧ acceleratedOrbit 13 1758 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1758 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1758) = 3 ^ 7 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1758.1, data_13_1758.2]

/-- Complete interval computation for depth 13, residue 1759. -/
theorem bounds_13_1759 : exactInterval 13 1759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1759 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1759) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1759 : oddCount 1759 13 = 7 ∧ acceleratedOrbit 13 1759 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1759 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1759) = 3 ^ 7 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1759.1, data_13_1759.2]

/-- Complete interval computation for depth 13, residue 1760. -/
theorem bounds_13_1760 : exactInterval 13 1760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1760 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1760) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1760 : oddCount 1760 13 = 6 ∧ acceleratedOrbit 13 1760 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1760 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1760) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1760.1, data_13_1760.2]

/-- Complete interval computation for depth 13, residue 1761. -/
theorem bounds_13_1761 : exactInterval 13 1761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1761 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1761) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1761 : oddCount 1761 13 = 9 ∧ acceleratedOrbit 13 1761 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1761 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1761) = 3 ^ 9 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1761.1, data_13_1761.2]

/-- Complete interval computation for depth 13, residue 1762. -/
theorem bounds_13_1762 : exactInterval 13 1762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1762 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1762) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1762 : oddCount 1762 13 = 6 ∧ acceleratedOrbit 13 1762 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1762 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1762) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1762.1, data_13_1762.2]

/-- Complete interval computation for depth 13, residue 1763. -/
theorem bounds_13_1763 : exactInterval 13 1763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1763 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1763) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1763 : oddCount 1763 13 = 6 ∧ acceleratedOrbit 13 1763 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1763 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1763) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1763.1, data_13_1763.2]

/-- Complete interval computation for depth 13, residue 1764. -/
theorem bounds_13_1764 : exactInterval 13 1764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1764 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1764) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1764 : oddCount 1764 13 = 5 ∧ acceleratedOrbit 13 1764 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1764 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1764) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1764.1, data_13_1764.2]

/-- Complete interval computation for depth 13, residue 1765. -/
theorem bounds_13_1765 : exactInterval 13 1765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1765 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1765) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1765 : oddCount 1765 13 = 5 ∧ acceleratedOrbit 13 1765 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1765 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1765) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1765.1, data_13_1765.2]

/-- Complete interval computation for depth 13, residue 1766. -/
theorem bounds_13_1766 : exactInterval 13 1766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1766 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1766) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1766 : oddCount 1766 13 = 5 ∧ acceleratedOrbit 13 1766 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1766 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1766) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1766.1, data_13_1766.2]

/-- Complete interval computation for depth 13, residue 1767. -/
theorem bounds_13_1767 : exactInterval 13 1767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1767 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1767) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1767 : oddCount 1767 13 = 9 ∧ acceleratedOrbit 13 1767 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1767 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1767) = 3 ^ 9 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1767.1, data_13_1767.2]

/-- Complete interval computation for depth 13, residue 1768. -/
theorem bounds_13_1768 : exactInterval 13 1768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1768 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1768) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1768 : oddCount 1768 13 = 6 ∧ acceleratedOrbit 13 1768 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1768 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1768) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1768.1, data_13_1768.2]

/-- Complete interval computation for depth 13, residue 1769. -/
theorem bounds_13_1769 : exactInterval 13 1769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1769 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1769) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1769 : oddCount 1769 13 = 9 ∧ acceleratedOrbit 13 1769 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1769 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1769) = 3 ^ 9 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1769.1, data_13_1769.2]

/-- Complete interval computation for depth 13, residue 1770. -/
theorem bounds_13_1770 : exactInterval 13 1770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1770 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1770) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1770 : oddCount 1770 13 = 6 ∧ acceleratedOrbit 13 1770 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1770 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1770) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1770.1, data_13_1770.2]

end Collatz.Research.StoppingAtlas.Batch0582
