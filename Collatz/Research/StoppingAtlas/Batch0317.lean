import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0317

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1781. -/
theorem bounds_12_1781 : exactInterval 12 1781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1781 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1781) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1781 : oddCount 1781 12 = 6 ∧ acceleratedOrbit 12 1781 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1781 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1781) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1781.1, data_12_1781.2]

/-- Complete interval computation for depth 12, residue 1782. -/
theorem bounds_12_1782 : exactInterval 12 1782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1782 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1782) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1782 : oddCount 1782 12 = 8 ∧ acceleratedOrbit 12 1782 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1782 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1782) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1782.1, data_12_1782.2]

/-- Complete interval computation for depth 12, residue 1783. -/
theorem bounds_12_1783 : exactInterval 12 1783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1783 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1783) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1783 : oddCount 1783 12 = 8 ∧ acceleratedOrbit 12 1783 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1783 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1783) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1783.1, data_12_1783.2]

/-- Complete interval computation for depth 12, residue 1784. -/
theorem bounds_12_1784 : exactInterval 12 1784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1784 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1784) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1784 : oddCount 1784 12 = 6 ∧ acceleratedOrbit 12 1784 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1784 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1784) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1784.1, data_12_1784.2]

/-- Complete interval computation for depth 12, residue 1785. -/
theorem bounds_12_1785 : exactInterval 12 1785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1785 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1785) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1785 : oddCount 1785 12 = 5 ∧ acceleratedOrbit 12 1785 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1785 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1785) = 3 ^ 5 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1785.1, data_12_1785.2]

/-- Complete interval computation for depth 12, residue 1786. -/
theorem bounds_12_1786 : exactInterval 12 1786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1786 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1786) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1786 : oddCount 1786 12 = 6 ∧ acceleratedOrbit 12 1786 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1786 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1786) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1786.1, data_12_1786.2]

/-- Complete interval computation for depth 12, residue 1787. -/
theorem bounds_12_1787 : exactInterval 12 1787 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1787 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1787) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1787 : oddCount 1787 12 = 7 ∧ acceleratedOrbit 12 1787 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1787 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1787) = 3 ^ 7 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1787.1, data_12_1787.2]

/-- Complete interval computation for depth 12, residue 1788. -/
theorem bounds_12_1788 : exactInterval 12 1788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1788 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1788) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1788 : oddCount 1788 12 = 9 ∧ acceleratedOrbit 12 1788 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1788 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1788) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1788.1, data_12_1788.2]

/-- Complete interval computation for depth 12, residue 1789. -/
theorem bounds_12_1789 : exactInterval 12 1789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1789 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1789) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1789 : oddCount 1789 12 = 9 ∧ acceleratedOrbit 12 1789 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1789 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1789) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1789.1, data_12_1789.2]

/-- Complete interval computation for depth 12, residue 1790. -/
theorem bounds_12_1790 : exactInterval 12 1790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1790 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1790) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1790 : oddCount 1790 12 = 9 ∧ acceleratedOrbit 12 1790 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1790 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1790) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1790.1, data_12_1790.2]

/-- Complete interval computation for depth 12, residue 1791. -/
theorem bounds_12_1791 : exactInterval 12 1791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1791 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1791) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1791 : oddCount 1791 12 = 10 ∧ acceleratedOrbit 12 1791 = 25834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1791 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1791) = 3 ^ 10 * m + 25834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1791.1, data_12_1791.2]

/-- Complete interval computation for depth 12, residue 1792. -/
theorem bounds_12_1792 : exactInterval 12 1792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1792 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1792) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1792 : oddCount 1792 12 = 3 ∧ acceleratedOrbit 12 1792 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1792 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1792) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1792.1, data_12_1792.2]

/-- Complete interval computation for depth 12, residue 1793. -/
theorem bounds_12_1793 : exactInterval 12 1793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1793 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1793) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1793 : oddCount 1793 12 = 5 ∧ acceleratedOrbit 12 1793 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1793 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1793) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1793.1, data_12_1793.2]

/-- Complete interval computation for depth 12, residue 1794. -/
theorem bounds_12_1794 : exactInterval 12 1794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1794 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1794) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1794 : oddCount 1794 12 = 7 ∧ acceleratedOrbit 12 1794 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1794 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1794) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1794.1, data_12_1794.2]

/-- Complete interval computation for depth 12, residue 1795. -/
theorem bounds_12_1795 : exactInterval 12 1795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1795 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1795) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1795 : oddCount 1795 12 = 7 ∧ acceleratedOrbit 12 1795 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1795 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1795) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1795.1, data_12_1795.2]

/-- Complete interval computation for depth 12, residue 1796. -/
theorem bounds_12_1796 : exactInterval 12 1796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1796 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1796) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1796 : oddCount 1796 12 = 6 ∧ acceleratedOrbit 12 1796 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1796 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1796) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1796.1, data_12_1796.2]

end Collatz.Research.StoppingAtlas.Batch0317
