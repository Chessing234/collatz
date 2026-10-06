import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0184

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1786. -/
theorem bounds_11_1786 : exactInterval 11 1786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1786 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1786) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1786 : oddCount 1786 11 = 6 ∧ acceleratedOrbit 11 1786 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1786 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1786) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1786.1, data_11_1786.2]

/-- Complete interval computation for depth 11, residue 1787. -/
theorem bounds_11_1787 : exactInterval 11 1787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1787 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1787) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1787 : oddCount 1787 11 = 7 ∧ acceleratedOrbit 11 1787 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1787 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1787) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1787.1, data_11_1787.2]

/-- Complete interval computation for depth 11, residue 1788. -/
theorem bounds_11_1788 : exactInterval 11 1788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1788 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1788) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1788 : oddCount 1788 11 = 8 ∧ acceleratedOrbit 11 1788 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1788 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1788) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1788.1, data_11_1788.2]

/-- Complete interval computation for depth 11, residue 1789. -/
theorem bounds_11_1789 : exactInterval 11 1789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1789 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1789) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1789 : oddCount 1789 11 = 8 ∧ acceleratedOrbit 11 1789 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1789 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1789) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1789.1, data_11_1789.2]

/-- Complete interval computation for depth 11, residue 1790. -/
theorem bounds_11_1790 : exactInterval 11 1790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1790 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1790) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1790 : oddCount 1790 11 = 8 ∧ acceleratedOrbit 11 1790 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1790 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1790) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1790.1, data_11_1790.2]

/-- Complete interval computation for depth 11, residue 1791. -/
theorem bounds_11_1791 : exactInterval 11 1791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1791 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1791) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1791 : oddCount 1791 11 = 10 ∧ acceleratedOrbit 11 1791 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1791 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1791) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1791.1, data_11_1791.2]

/-- Complete interval computation for depth 11, residue 1792. -/
theorem bounds_11_1792 : exactInterval 11 1792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1792 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1792) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1792 : oddCount 1792 11 = 3 ∧ acceleratedOrbit 11 1792 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1792 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1792) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1792.1, data_11_1792.2]

/-- Complete interval computation for depth 11, residue 1793. -/
theorem bounds_11_1793 : exactInterval 11 1793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1793 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1793) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1793 : oddCount 1793 11 = 4 ∧ acceleratedOrbit 11 1793 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1793 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1793) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1793.1, data_11_1793.2]

/-- Complete interval computation for depth 11, residue 1794. -/
theorem bounds_11_1794 : exactInterval 11 1794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1794 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1794) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1794 : oddCount 1794 11 = 6 ∧ acceleratedOrbit 11 1794 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1794 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1794) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1794.1, data_11_1794.2]

/-- Complete interval computation for depth 11, residue 1795. -/
theorem bounds_11_1795 : exactInterval 11 1795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1795 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1795) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1795 : oddCount 1795 11 = 6 ∧ acceleratedOrbit 11 1795 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1795 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1795) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1795.1, data_11_1795.2]

/-- Complete interval computation for depth 11, residue 1796. -/
theorem bounds_11_1796 : exactInterval 11 1796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1796 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1796) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1796 : oddCount 1796 11 = 5 ∧ acceleratedOrbit 11 1796 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1796 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1796) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1796.1, data_11_1796.2]

/-- Complete interval computation for depth 11, residue 1797. -/
theorem bounds_11_1797 : exactInterval 11 1797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1797 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1797) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1797 : oddCount 1797 11 = 5 ∧ acceleratedOrbit 11 1797 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1797 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1797) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1797.1, data_11_1797.2]

/-- Complete interval computation for depth 11, residue 1798. -/
theorem bounds_11_1798 : exactInterval 11 1798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1798 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1798) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1798 : oddCount 1798 11 = 5 ∧ acceleratedOrbit 11 1798 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1798 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1798) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1798.1, data_11_1798.2]

/-- Complete interval computation for depth 11, residue 1799. -/
theorem bounds_11_1799 : exactInterval 11 1799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1799 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1799) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1799 : oddCount 1799 11 = 6 ∧ acceleratedOrbit 11 1799 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1799 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1799) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1799.1, data_11_1799.2]

/-- Complete interval computation for depth 11, residue 1800. -/
theorem bounds_11_1800 : exactInterval 11 1800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1800 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1800) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1800 : oddCount 1800 11 = 6 ∧ acceleratedOrbit 11 1800 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1800 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1800) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1800.1, data_11_1800.2]

/-- Complete interval computation for depth 11, residue 1801. -/
theorem bounds_11_1801 : exactInterval 11 1801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1801 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1801) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1801 : oddCount 1801 11 = 8 ∧ acceleratedOrbit 11 1801 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1801 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1801) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1801.1, data_11_1801.2]

end Collatz.Research.StoppingAtlas.Batch0184
