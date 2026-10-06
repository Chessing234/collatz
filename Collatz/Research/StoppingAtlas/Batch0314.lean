import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0314

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1735. -/
theorem bounds_12_1735 : exactInterval 12 1735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1735 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1735) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1735 : oddCount 1735 12 = 5 ∧ acceleratedOrbit 12 1735 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1735 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1735) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1735.1, data_12_1735.2]

/-- Complete interval computation for depth 12, residue 1736. -/
theorem bounds_12_1736 : exactInterval 12 1736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1736 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1736) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1736 : oddCount 1736 12 = 4 ∧ acceleratedOrbit 12 1736 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1736 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1736) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1736.1, data_12_1736.2]

/-- Complete interval computation for depth 12, residue 1737. -/
theorem bounds_12_1737 : exactInterval 12 1737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1737 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1737) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1737 : oddCount 1737 12 = 6 ∧ acceleratedOrbit 12 1737 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1737 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1737) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1737.1, data_12_1737.2]

/-- Complete interval computation for depth 12, residue 1738. -/
theorem bounds_12_1738 : exactInterval 12 1738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1738 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1738) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1738 : oddCount 1738 12 = 4 ∧ acceleratedOrbit 12 1738 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1738 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1738) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1738.1, data_12_1738.2]

/-- Complete interval computation for depth 12, residue 1739. -/
theorem bounds_12_1739 : exactInterval 12 1739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1739 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1739) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1739 : oddCount 1739 12 = 7 ∧ acceleratedOrbit 12 1739 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1739 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1739) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1739.1, data_12_1739.2]

/-- Complete interval computation for depth 12, residue 1740. -/
theorem bounds_12_1740 : exactInterval 12 1740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1740 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1740) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1740 : oddCount 1740 12 = 4 ∧ acceleratedOrbit 12 1740 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1740 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1740) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1740.1, data_12_1740.2]

/-- Complete interval computation for depth 12, residue 1741. -/
theorem bounds_12_1741 : exactInterval 12 1741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1741 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1741) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1741 : oddCount 1741 12 = 4 ∧ acceleratedOrbit 12 1741 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1741 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1741) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1741.1, data_12_1741.2]

/-- Complete interval computation for depth 12, residue 1742. -/
theorem bounds_12_1742 : exactInterval 12 1742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1742 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1742) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1742 : oddCount 1742 12 = 9 ∧ acceleratedOrbit 12 1742 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1742 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1742) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1742.1, data_12_1742.2]

/-- Complete interval computation for depth 12, residue 1743. -/
theorem bounds_12_1743 : exactInterval 12 1743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1743 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1743) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1743 : oddCount 1743 12 = 9 ∧ acceleratedOrbit 12 1743 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1743 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1743) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1743.1, data_12_1743.2]

/-- Complete interval computation for depth 12, residue 1744. -/
theorem bounds_12_1744 : exactInterval 12 1744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1744 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1744) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1744 : oddCount 1744 12 = 5 ∧ acceleratedOrbit 12 1744 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1744 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1744) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1744.1, data_12_1744.2]

/-- Complete interval computation for depth 12, residue 1745. -/
theorem bounds_12_1745 : exactInterval 12 1745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1745 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1745) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1745 : oddCount 1745 12 = 7 ∧ acceleratedOrbit 12 1745 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1745 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1745) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1745.1, data_12_1745.2]

/-- Complete interval computation for depth 12, residue 1746. -/
theorem bounds_12_1746 : exactInterval 12 1746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1746 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1746) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1746 : oddCount 1746 12 = 7 ∧ acceleratedOrbit 12 1746 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1746 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1746) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1746.1, data_12_1746.2]

/-- Complete interval computation for depth 12, residue 1747. -/
theorem bounds_12_1747 : exactInterval 12 1747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1747 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1747) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1747 : oddCount 1747 12 = 7 ∧ acceleratedOrbit 12 1747 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1747 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1747) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1747.1, data_12_1747.2]

/-- Complete interval computation for depth 12, residue 1748. -/
theorem bounds_12_1748 : exactInterval 12 1748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1748 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1748) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1748 : oddCount 1748 12 = 5 ∧ acceleratedOrbit 12 1748 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1748 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1748) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1748.1, data_12_1748.2]

/-- Complete interval computation for depth 12, residue 1749. -/
theorem bounds_12_1749 : exactInterval 12 1749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1749 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1749) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1749 : oddCount 1749 12 = 5 ∧ acceleratedOrbit 12 1749 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1749 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1749) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1749.1, data_12_1749.2]

/-- Complete interval computation for depth 12, residue 1750. -/
theorem bounds_12_1750 : exactInterval 12 1750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1750 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1750) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1750 : oddCount 1750 12 = 5 ∧ acceleratedOrbit 12 1750 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1750 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1750) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1750.1, data_12_1750.2]

end Collatz.Research.StoppingAtlas.Batch0314
