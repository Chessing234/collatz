import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0054

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1736. -/
theorem bounds_15_1736 : exactInterval 15 1736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1736 : oddCount 1736 15 = 6 ∧ acceleratedOrbit 15 1736 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1736) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1736.1, data_15_1736.2]

/-- Complete interval computation for depth 15, residue 1737. -/
theorem bounds_15_1737 : exactInterval 15 1737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1737 : oddCount 1737 15 = 8 ∧ acceleratedOrbit 15 1737 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1737) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1737.1, data_15_1737.2]

/-- Complete interval computation for depth 15, residue 1738. -/
theorem bounds_15_1738 : exactInterval 15 1738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1738 : oddCount 1738 15 = 6 ∧ acceleratedOrbit 15 1738 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1738) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1738.1, data_15_1738.2]

/-- Complete interval computation for depth 15, residue 1739. -/
theorem bounds_15_1739 : exactInterval 15 1739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1739 : oddCount 1739 15 = 9 ∧ acceleratedOrbit 15 1739 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1739) = 3 ^ 9 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1739.1, data_15_1739.2]

/-- Complete interval computation for depth 15, residue 1740. -/
theorem bounds_15_1740 : exactInterval 15 1740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1740 : oddCount 1740 15 = 6 ∧ acceleratedOrbit 15 1740 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1740) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1740.1, data_15_1740.2]

/-- Complete interval computation for depth 15, residue 1741. -/
theorem bounds_15_1741 : exactInterval 15 1741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1741 : oddCount 1741 15 = 6 ∧ acceleratedOrbit 15 1741 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1741) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1741.1, data_15_1741.2]

/-- Complete interval computation for depth 15, residue 1742. -/
theorem bounds_15_1742 : exactInterval 15 1742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1742 : oddCount 1742 15 = 12 ∧ acceleratedOrbit 15 1742 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1742) = 3 ^ 12 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1742.1, data_15_1742.2]

/-- Complete interval computation for depth 15, residue 1743. -/
theorem bounds_15_1743 : exactInterval 15 1743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1743 : oddCount 1743 15 = 12 ∧ acceleratedOrbit 15 1743 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1743) = 3 ^ 12 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1743.1, data_15_1743.2]

/-- Complete interval computation for depth 15, residue 1744. -/
theorem bounds_15_1744 : exactInterval 15 1744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1744 : oddCount 1744 15 = 7 ∧ acceleratedOrbit 15 1744 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1744) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1744.1, data_15_1744.2]

/-- Complete interval computation for depth 15, residue 1745. -/
theorem bounds_15_1745 : exactInterval 15 1745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1745 : oddCount 1745 15 = 10 ∧ acceleratedOrbit 15 1745 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1745) = 3 ^ 10 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1745.1, data_15_1745.2]

/-- Complete interval computation for depth 15, residue 1746. -/
theorem bounds_15_1746 : exactInterval 15 1746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1746 : oddCount 1746 15 = 10 ∧ acceleratedOrbit 15 1746 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1746) = 3 ^ 10 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1746.1, data_15_1746.2]

/-- Complete interval computation for depth 15, residue 1747. -/
theorem bounds_15_1747 : exactInterval 15 1747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1747 : oddCount 1747 15 = 10 ∧ acceleratedOrbit 15 1747 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1747) = 3 ^ 10 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1747.1, data_15_1747.2]

/-- Complete interval computation for depth 15, residue 1748. -/
theorem bounds_15_1748 : exactInterval 15 1748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1748 : oddCount 1748 15 = 7 ∧ acceleratedOrbit 15 1748 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1748) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1748.1, data_15_1748.2]

/-- Complete interval computation for depth 15, residue 1749. -/
theorem bounds_15_1749 : exactInterval 15 1749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1749 : oddCount 1749 15 = 7 ∧ acceleratedOrbit 15 1749 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1749) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1749.1, data_15_1749.2]

/-- Complete interval computation for depth 15, residue 1750. -/
theorem bounds_15_1750 : exactInterval 15 1750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1750 : oddCount 1750 15 = 5 ∧ acceleratedOrbit 15 1750 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1750) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1750.1, data_15_1750.2]

/-- Complete interval computation for depth 15, residue 1751. -/
theorem bounds_15_1751 : exactInterval 15 1751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1751 : oddCount 1751 15 = 5 ∧ acceleratedOrbit 15 1751 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1751) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1751.1, data_15_1751.2]

/-- Complete interval computation for depth 15, residue 1752. -/
theorem bounds_15_1752 : exactInterval 15 1752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1752 : oddCount 1752 15 = 7 ∧ acceleratedOrbit 15 1752 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1752) = 3 ^ 7 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1752.1, data_15_1752.2]

/-- Complete interval computation for depth 15, residue 1753. -/
theorem bounds_15_1753 : exactInterval 15 1753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1753 : oddCount 1753 15 = 7 ∧ acceleratedOrbit 15 1753 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1753) = 3 ^ 7 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1753.1, data_15_1753.2]

/-- Complete interval computation for depth 15, residue 1754. -/
theorem bounds_15_1754 : exactInterval 15 1754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1754 : oddCount 1754 15 = 7 ∧ acceleratedOrbit 15 1754 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1754) = 3 ^ 7 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1754.1, data_15_1754.2]

/-- Complete interval computation for depth 15, residue 1755. -/
theorem bounds_15_1755 : exactInterval 15 1755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1755 : oddCount 1755 15 = 8 ∧ acceleratedOrbit 15 1755 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1755) = 3 ^ 8 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1755.1, data_15_1755.2]

/-- Complete interval computation for depth 15, residue 1756. -/
theorem bounds_15_1756 : exactInterval 15 1756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1756 : oddCount 1756 15 = 7 ∧ acceleratedOrbit 15 1756 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1756) = 3 ^ 7 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1756.1, data_15_1756.2]

/-- Complete interval computation for depth 15, residue 1757. -/
theorem bounds_15_1757 : exactInterval 15 1757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1757 : oddCount 1757 15 = 7 ∧ acceleratedOrbit 15 1757 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1757) = 3 ^ 7 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1757.1, data_15_1757.2]

/-- Complete interval computation for depth 15, residue 1758. -/
theorem bounds_15_1758 : exactInterval 15 1758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1758 : oddCount 1758 15 = 8 ∧ acceleratedOrbit 15 1758 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1758) = 3 ^ 8 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1758.1, data_15_1758.2]

/-- Complete interval computation for depth 15, residue 1759. -/
theorem bounds_15_1759 : exactInterval 15 1759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1759 : oddCount 1759 15 = 8 ∧ acceleratedOrbit 15 1759 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1759) = 3 ^ 8 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1759.1, data_15_1759.2]

/-- Complete interval computation for depth 15, residue 1760. -/
theorem bounds_15_1760 : exactInterval 15 1760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1760 : oddCount 1760 15 = 7 ∧ acceleratedOrbit 15 1760 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1760) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1760.1, data_15_1760.2]

/-- Complete interval computation for depth 15, residue 1761. -/
theorem bounds_15_1761 : exactInterval 15 1761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1761 : oddCount 1761 15 = 10 ∧ acceleratedOrbit 15 1761 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1761) = 3 ^ 10 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1761.1, data_15_1761.2]

/-- Complete interval computation for depth 15, residue 1762. -/
theorem bounds_15_1762 : exactInterval 15 1762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1762 : oddCount 1762 15 = 7 ∧ acceleratedOrbit 15 1762 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1762) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1762.1, data_15_1762.2]

/-- Complete interval computation for depth 15, residue 1763. -/
theorem bounds_15_1763 : exactInterval 15 1763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1763 : oddCount 1763 15 = 7 ∧ acceleratedOrbit 15 1763 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1763) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1763.1, data_15_1763.2]

/-- Complete interval computation for depth 15, residue 1764. -/
theorem bounds_15_1764 : exactInterval 15 1764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1764 : oddCount 1764 15 = 6 ∧ acceleratedOrbit 15 1764 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1764) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1764.1, data_15_1764.2]

/-- Complete interval computation for depth 15, residue 1765. -/
theorem bounds_15_1765 : exactInterval 15 1765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1765 : oddCount 1765 15 = 6 ∧ acceleratedOrbit 15 1765 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1765) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1765.1, data_15_1765.2]

/-- Complete interval computation for depth 15, residue 1766. -/
theorem bounds_15_1766 : exactInterval 15 1766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1766 : oddCount 1766 15 = 6 ∧ acceleratedOrbit 15 1766 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1766) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1766.1, data_15_1766.2]

/-- Complete interval computation for depth 15, residue 1767. -/
theorem bounds_15_1767 : exactInterval 15 1767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1767 : oddCount 1767 15 = 10 ∧ acceleratedOrbit 15 1767 = 3187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1767) = 3 ^ 10 * m + 3187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1767.1, data_15_1767.2]

/-- Complete interval computation for depth 15, residue 1768. -/
theorem bounds_15_1768 : exactInterval 15 1768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1768 : oddCount 1768 15 = 7 ∧ acceleratedOrbit 15 1768 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1768) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1768.1, data_15_1768.2]

end Collatz.Research.PassageAtlas.Batch0054
