import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0182

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1756. -/
theorem bounds_11_1756 : exactInterval 11 1756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1756 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1756) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1756 : oddCount 1756 11 = 5 ∧ acceleratedOrbit 11 1756 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1756 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1756) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1756.1, data_11_1756.2]

/-- Complete interval computation for depth 11, residue 1757. -/
theorem bounds_11_1757 : exactInterval 11 1757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1757 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1757) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1757 : oddCount 1757 11 = 5 ∧ acceleratedOrbit 11 1757 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1757 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1757) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1757.1, data_11_1757.2]

/-- Complete interval computation for depth 11, residue 1758. -/
theorem bounds_11_1758 : exactInterval 11 1758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1758 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1758) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1758 : oddCount 1758 11 = 7 ∧ acceleratedOrbit 11 1758 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1758 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1758) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1758.1, data_11_1758.2]

/-- Complete interval computation for depth 11, residue 1759. -/
theorem bounds_11_1759 : exactInterval 11 1759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1759 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1759) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1759 : oddCount 1759 11 = 7 ∧ acceleratedOrbit 11 1759 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1759 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1759) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1759.1, data_11_1759.2]

/-- Complete interval computation for depth 11, residue 1760. -/
theorem bounds_11_1760 : exactInterval 11 1760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1760 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1760) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1760 : oddCount 1760 11 = 4 ∧ acceleratedOrbit 11 1760 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1760 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1760) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1760.1, data_11_1760.2]

/-- Complete interval computation for depth 11, residue 1761. -/
theorem bounds_11_1761 : exactInterval 11 1761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1761 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1761) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1761 : oddCount 1761 11 = 7 ∧ acceleratedOrbit 11 1761 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1761 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1761) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1761.1, data_11_1761.2]

/-- Complete interval computation for depth 11, residue 1762. -/
theorem bounds_11_1762 : exactInterval 11 1762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1762 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1762) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1762 : oddCount 1762 11 = 4 ∧ acceleratedOrbit 11 1762 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1762 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1762) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1762.1, data_11_1762.2]

/-- Complete interval computation for depth 11, residue 1763. -/
theorem bounds_11_1763 : exactInterval 11 1763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1763 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1763) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1763 : oddCount 1763 11 = 4 ∧ acceleratedOrbit 11 1763 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1763 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1763) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1763.1, data_11_1763.2]

/-- Complete interval computation for depth 11, residue 1764. -/
theorem bounds_11_1764 : exactInterval 11 1764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1764 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1764) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1764 : oddCount 1764 11 = 4 ∧ acceleratedOrbit 11 1764 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1764 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1764) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1764.1, data_11_1764.2]

/-- Complete interval computation for depth 11, residue 1765. -/
theorem bounds_11_1765 : exactInterval 11 1765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1765 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1765) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1765 : oddCount 1765 11 = 4 ∧ acceleratedOrbit 11 1765 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1765 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1765) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1765.1, data_11_1765.2]

/-- Complete interval computation for depth 11, residue 1766. -/
theorem bounds_11_1766 : exactInterval 11 1766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1766 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1766) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1766 : oddCount 1766 11 = 4 ∧ acceleratedOrbit 11 1766 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1766 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1766) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1766.1, data_11_1766.2]

/-- Complete interval computation for depth 11, residue 1767. -/
theorem bounds_11_1767 : exactInterval 11 1767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1767 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1767) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1767 : oddCount 1767 11 = 8 ∧ acceleratedOrbit 11 1767 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1767 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1767) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1767.1, data_11_1767.2]

/-- Complete interval computation for depth 11, residue 1768. -/
theorem bounds_11_1768 : exactInterval 11 1768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1768 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1768) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1768 : oddCount 1768 11 = 4 ∧ acceleratedOrbit 11 1768 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1768 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1768) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1768.1, data_11_1768.2]

/-- Complete interval computation for depth 11, residue 1769. -/
theorem bounds_11_1769 : exactInterval 11 1769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1769 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1769) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1769 : oddCount 1769 11 = 7 ∧ acceleratedOrbit 11 1769 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1769 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1769) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1769.1, data_11_1769.2]

/-- Complete interval computation for depth 11, residue 1770. -/
theorem bounds_11_1770 : exactInterval 11 1770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1770 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1770) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1770 : oddCount 1770 11 = 4 ∧ acceleratedOrbit 11 1770 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1770 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1770) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1770.1, data_11_1770.2]

end Collatz.Research.StoppingAtlas.Batch0182
