import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0315

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1751. -/
theorem bounds_12_1751 : exactInterval 12 1751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1751 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1751) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1751 : oddCount 1751 12 = 5 ∧ acceleratedOrbit 12 1751 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1751 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1751) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1751.1, data_12_1751.2]

/-- Complete interval computation for depth 12, residue 1752. -/
theorem bounds_12_1752 : exactInterval 12 1752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1752 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1752) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1752 : oddCount 1752 12 = 6 ∧ acceleratedOrbit 12 1752 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1752 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1752) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1752.1, data_12_1752.2]

/-- Complete interval computation for depth 12, residue 1753. -/
theorem bounds_12_1753 : exactInterval 12 1753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1753 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1753) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1753 : oddCount 1753 12 = 6 ∧ acceleratedOrbit 12 1753 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1753 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1753) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1753.1, data_12_1753.2]

/-- Complete interval computation for depth 12, residue 1754. -/
theorem bounds_12_1754 : exactInterval 12 1754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1754 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1754) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1754 : oddCount 1754 12 = 6 ∧ acceleratedOrbit 12 1754 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1754 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1754) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1754.1, data_12_1754.2]

/-- Complete interval computation for depth 12, residue 1755. -/
theorem bounds_12_1755 : exactInterval 12 1755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1755 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1755) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1755 : oddCount 1755 12 = 7 ∧ acceleratedOrbit 12 1755 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1755 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1755) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1755.1, data_12_1755.2]

/-- Complete interval computation for depth 12, residue 1756. -/
theorem bounds_12_1756 : exactInterval 12 1756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1756 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1756) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1756 : oddCount 1756 12 = 6 ∧ acceleratedOrbit 12 1756 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1756 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1756) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1756.1, data_12_1756.2]

/-- Complete interval computation for depth 12, residue 1757. -/
theorem bounds_12_1757 : exactInterval 12 1757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1757 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1757) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1757 : oddCount 1757 12 = 6 ∧ acceleratedOrbit 12 1757 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1757 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1757) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1757.1, data_12_1757.2]

/-- Complete interval computation for depth 12, residue 1758. -/
theorem bounds_12_1758 : exactInterval 12 1758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1758 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1758) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1758 : oddCount 1758 12 = 7 ∧ acceleratedOrbit 12 1758 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1758 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1758) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1758.1, data_12_1758.2]

/-- Complete interval computation for depth 12, residue 1759. -/
theorem bounds_12_1759 : exactInterval 12 1759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1759 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1759) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1759 : oddCount 1759 12 = 7 ∧ acceleratedOrbit 12 1759 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1759 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1759) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1759.1, data_12_1759.2]

/-- Complete interval computation for depth 12, residue 1760. -/
theorem bounds_12_1760 : exactInterval 12 1760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1760 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1760) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1760 : oddCount 1760 12 = 5 ∧ acceleratedOrbit 12 1760 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1760 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1760) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1760.1, data_12_1760.2]

/-- Complete interval computation for depth 12, residue 1761. -/
theorem bounds_12_1761 : exactInterval 12 1761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1761 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1761) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1761 : oddCount 1761 12 = 8 ∧ acceleratedOrbit 12 1761 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1761 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1761) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1761.1, data_12_1761.2]

/-- Complete interval computation for depth 12, residue 1762. -/
theorem bounds_12_1762 : exactInterval 12 1762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1762 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1762) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1762 : oddCount 1762 12 = 5 ∧ acceleratedOrbit 12 1762 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1762 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1762) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1762.1, data_12_1762.2]

/-- Complete interval computation for depth 12, residue 1763. -/
theorem bounds_12_1763 : exactInterval 12 1763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1763 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1763) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1763 : oddCount 1763 12 = 5 ∧ acceleratedOrbit 12 1763 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1763 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1763) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1763.1, data_12_1763.2]

/-- Complete interval computation for depth 12, residue 1764. -/
theorem bounds_12_1764 : exactInterval 12 1764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1764 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1764) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1764 : oddCount 1764 12 = 4 ∧ acceleratedOrbit 12 1764 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1764 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1764) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1764.1, data_12_1764.2]

/-- Complete interval computation for depth 12, residue 1765. -/
theorem bounds_12_1765 : exactInterval 12 1765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1765 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1765) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1765 : oddCount 1765 12 = 4 ∧ acceleratedOrbit 12 1765 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1765 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1765) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1765.1, data_12_1765.2]

end Collatz.Research.StoppingAtlas.Batch0315
