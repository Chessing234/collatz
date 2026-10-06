import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0581

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1740. -/
theorem bounds_13_1740 : exactInterval 13 1740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1740 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1740) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1740 : oddCount 1740 13 = 5 ∧ acceleratedOrbit 13 1740 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1740 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1740) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1740.1, data_13_1740.2]

/-- Complete interval computation for depth 13, residue 1741. -/
theorem bounds_13_1741 : exactInterval 13 1741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1741 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1741) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1741 : oddCount 1741 13 = 5 ∧ acceleratedOrbit 13 1741 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1741 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1741) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1741.1, data_13_1741.2]

/-- Complete interval computation for depth 13, residue 1742. -/
theorem bounds_13_1742 : exactInterval 13 1742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1742 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1742) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1742 : oddCount 1742 13 = 10 ∧ acceleratedOrbit 13 1742 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1742 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1742) = 3 ^ 10 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1742.1, data_13_1742.2]

/-- Complete interval computation for depth 13, residue 1743. -/
theorem bounds_13_1743 : exactInterval 13 1743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1743 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1743) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1743 : oddCount 1743 13 = 10 ∧ acceleratedOrbit 13 1743 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1743 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1743) = 3 ^ 10 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1743.1, data_13_1743.2]

/-- Complete interval computation for depth 13, residue 1744. -/
theorem bounds_13_1744 : exactInterval 13 1744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1744 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1744) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1744 : oddCount 1744 13 = 6 ∧ acceleratedOrbit 13 1744 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1744 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1744) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1744.1, data_13_1744.2]

/-- Complete interval computation for depth 13, residue 1745. -/
theorem bounds_13_1745 : exactInterval 13 1745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1745 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1745) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1745 : oddCount 1745 13 = 8 ∧ acceleratedOrbit 13 1745 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1745 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1745) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1745.1, data_13_1745.2]

/-- Complete interval computation for depth 13, residue 1746. -/
theorem bounds_13_1746 : exactInterval 13 1746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1746 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1746) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1746 : oddCount 1746 13 = 8 ∧ acceleratedOrbit 13 1746 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1746 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1746) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1746.1, data_13_1746.2]

/-- Complete interval computation for depth 13, residue 1747. -/
theorem bounds_13_1747 : exactInterval 13 1747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1747 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1747) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1747 : oddCount 1747 13 = 8 ∧ acceleratedOrbit 13 1747 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1747 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1747) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1747.1, data_13_1747.2]

/-- Complete interval computation for depth 13, residue 1748. -/
theorem bounds_13_1748 : exactInterval 13 1748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1748 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1748) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1748 : oddCount 1748 13 = 6 ∧ acceleratedOrbit 13 1748 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1748 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1748) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1748.1, data_13_1748.2]

/-- Complete interval computation for depth 13, residue 1749. -/
theorem bounds_13_1749 : exactInterval 13 1749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1749 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1749) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1749 : oddCount 1749 13 = 6 ∧ acceleratedOrbit 13 1749 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1749 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1749) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1749.1, data_13_1749.2]

/-- Complete interval computation for depth 13, residue 1750. -/
theorem bounds_13_1750 : exactInterval 13 1750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1750 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1750) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1750 : oddCount 1750 13 = 5 ∧ acceleratedOrbit 13 1750 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1750 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1750) = 3 ^ 5 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1750.1, data_13_1750.2]

/-- Complete interval computation for depth 13, residue 1751. -/
theorem bounds_13_1751 : exactInterval 13 1751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1751 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1751) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1751 : oddCount 1751 13 = 5 ∧ acceleratedOrbit 13 1751 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1751 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1751) = 3 ^ 5 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1751.1, data_13_1751.2]

/-- Complete interval computation for depth 13, residue 1752. -/
theorem bounds_13_1752 : exactInterval 13 1752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1752 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1752) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1752 : oddCount 1752 13 = 6 ∧ acceleratedOrbit 13 1752 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1752 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1752) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1752.1, data_13_1752.2]

/-- Complete interval computation for depth 13, residue 1753. -/
theorem bounds_13_1753 : exactInterval 13 1753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1753 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1753) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1753 : oddCount 1753 13 = 6 ∧ acceleratedOrbit 13 1753 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1753 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1753) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1753.1, data_13_1753.2]

/-- Complete interval computation for depth 13, residue 1754. -/
theorem bounds_13_1754 : exactInterval 13 1754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1754 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1754) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1754 : oddCount 1754 13 = 6 ∧ acceleratedOrbit 13 1754 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1754 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1754) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1754.1, data_13_1754.2]

/-- Complete interval computation for depth 13, residue 1755. -/
theorem bounds_13_1755 : exactInterval 13 1755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1755 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1755) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1755 : oddCount 1755 13 = 7 ∧ acceleratedOrbit 13 1755 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1755 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1755) = 3 ^ 7 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1755.1, data_13_1755.2]

end Collatz.Research.StoppingAtlas.Batch0581
