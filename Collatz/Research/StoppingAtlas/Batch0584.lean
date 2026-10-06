import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0584

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1786. -/
theorem bounds_13_1786 : exactInterval 13 1786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1786 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1786) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1786 : oddCount 1786 13 = 7 ∧ acceleratedOrbit 13 1786 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1786 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1786) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1786.1, data_13_1786.2]

/-- Complete interval computation for depth 13, residue 1787. -/
theorem bounds_13_1787 : exactInterval 13 1787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1787 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1787) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1787 : oddCount 1787 13 = 8 ∧ acceleratedOrbit 13 1787 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1787 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1787) = 3 ^ 8 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1787.1, data_13_1787.2]

/-- Complete interval computation for depth 13, residue 1788. -/
theorem bounds_13_1788 : exactInterval 13 1788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1788 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1788) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1788 : oddCount 1788 13 = 9 ∧ acceleratedOrbit 13 1788 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1788 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1788) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1788.1, data_13_1788.2]

/-- Complete interval computation for depth 13, residue 1789. -/
theorem bounds_13_1789 : exactInterval 13 1789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1789 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1789) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1789 : oddCount 1789 13 = 9 ∧ acceleratedOrbit 13 1789 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1789 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1789) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1789.1, data_13_1789.2]

/-- Complete interval computation for depth 13, residue 1790. -/
theorem bounds_13_1790 : exactInterval 13 1790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1790 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1790) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1790 : oddCount 1790 13 = 9 ∧ acceleratedOrbit 13 1790 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1790 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1790) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1790.1, data_13_1790.2]

/-- Complete interval computation for depth 13, residue 1791. -/
theorem bounds_13_1791 : exactInterval 13 1791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1791 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1791) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1791 : oddCount 1791 13 = 10 ∧ acceleratedOrbit 13 1791 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1791 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1791) = 3 ^ 10 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1791.1, data_13_1791.2]

/-- Complete interval computation for depth 13, residue 1792. -/
theorem bounds_13_1792 : exactInterval 13 1792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1792 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1792) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1792 : oddCount 1792 13 = 4 ∧ acceleratedOrbit 13 1792 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1792 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1792) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1792.1, data_13_1792.2]

/-- Complete interval computation for depth 13, residue 1793. -/
theorem bounds_13_1793 : exactInterval 13 1793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1793 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1793) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1793 : oddCount 1793 13 = 6 ∧ acceleratedOrbit 13 1793 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1793 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1793) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1793.1, data_13_1793.2]

/-- Complete interval computation for depth 13, residue 1794. -/
theorem bounds_13_1794 : exactInterval 13 1794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1794 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1794) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1794 : oddCount 1794 13 = 7 ∧ acceleratedOrbit 13 1794 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1794 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1794) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1794.1, data_13_1794.2]

/-- Complete interval computation for depth 13, residue 1795. -/
theorem bounds_13_1795 : exactInterval 13 1795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1795 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1795) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1795 : oddCount 1795 13 = 7 ∧ acceleratedOrbit 13 1795 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1795 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1795) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1795.1, data_13_1795.2]

/-- Complete interval computation for depth 13, residue 1796. -/
theorem bounds_13_1796 : exactInterval 13 1796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1796 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1796) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1796 : oddCount 1796 13 = 7 ∧ acceleratedOrbit 13 1796 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1796 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1796) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1796.1, data_13_1796.2]

/-- Complete interval computation for depth 13, residue 1797. -/
theorem bounds_13_1797 : exactInterval 13 1797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1797 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1797) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1797 : oddCount 1797 13 = 7 ∧ acceleratedOrbit 13 1797 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1797 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1797) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1797.1, data_13_1797.2]

/-- Complete interval computation for depth 13, residue 1798. -/
theorem bounds_13_1798 : exactInterval 13 1798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1798 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1798) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1798 : oddCount 1798 13 = 7 ∧ acceleratedOrbit 13 1798 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1798 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1798) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1798.1, data_13_1798.2]

/-- Complete interval computation for depth 13, residue 1799. -/
theorem bounds_13_1799 : exactInterval 13 1799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1799 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1799) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1799 : oddCount 1799 13 = 7 ∧ acceleratedOrbit 13 1799 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1799 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1799) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1799.1, data_13_1799.2]

/-- Complete interval computation for depth 13, residue 1800. -/
theorem bounds_13_1800 : exactInterval 13 1800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1800 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1800) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1800 : oddCount 1800 13 = 8 ∧ acceleratedOrbit 13 1800 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1800 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1800) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1800.1, data_13_1800.2]

/-- Complete interval computation for depth 13, residue 1801. -/
theorem bounds_13_1801 : exactInterval 13 1801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1801 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1801) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1801 : oddCount 1801 13 = 9 ∧ acceleratedOrbit 13 1801 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1801 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1801) = 3 ^ 9 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1801.1, data_13_1801.2]

end Collatz.Research.StoppingAtlas.Batch0584
