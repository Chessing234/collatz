import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0586

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1817. -/
theorem bounds_13_1817 : exactInterval 13 1817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1817 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1817) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1817 : oddCount 1817 13 = 10 ∧ acceleratedOrbit 13 1817 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1817 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1817) = 3 ^ 10 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1817.1, data_13_1817.2]

/-- Complete interval computation for depth 13, residue 1818. -/
theorem bounds_13_1818 : exactInterval 13 1818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1818 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1818) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1818 : oddCount 1818 13 = 2 ∧ acceleratedOrbit 13 1818 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1818 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1818) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1818.1, data_13_1818.2]

/-- Complete interval computation for depth 13, residue 1819. -/
theorem bounds_13_1819 : exactInterval 13 1819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1819 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1819) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1819 : oddCount 1819 13 = 12 ∧ acceleratedOrbit 13 1819 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1819 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1819) = 3 ^ 12 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1819.1, data_13_1819.2]

/-- Complete interval computation for depth 13, residue 1820. -/
theorem bounds_13_1820 : exactInterval 13 1820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1820 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1820) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1820 : oddCount 1820 13 = 7 ∧ acceleratedOrbit 13 1820 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1820 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1820) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1820.1, data_13_1820.2]

/-- Complete interval computation for depth 13, residue 1821. -/
theorem bounds_13_1821 : exactInterval 13 1821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1821 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1821) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1821 : oddCount 1821 13 = 7 ∧ acceleratedOrbit 13 1821 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1821 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1821) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1821.1, data_13_1821.2]

/-- Complete interval computation for depth 13, residue 1822. -/
theorem bounds_13_1822 : exactInterval 13 1822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1822 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1822) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1822 : oddCount 1822 13 = 7 ∧ acceleratedOrbit 13 1822 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1822 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1822) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1822.1, data_13_1822.2]

/-- Complete interval computation for depth 13, residue 1823. -/
theorem bounds_13_1823 : exactInterval 13 1823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1823 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1823) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1823 : oddCount 1823 13 = 7 ∧ acceleratedOrbit 13 1823 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1823 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1823) = 3 ^ 7 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1823.1, data_13_1823.2]

/-- Complete interval computation for depth 13, residue 1824. -/
theorem bounds_13_1824 : exactInterval 13 1824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1824 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1824) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1824 : oddCount 1824 13 = 5 ∧ acceleratedOrbit 13 1824 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1824 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1824) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1824.1, data_13_1824.2]

/-- Complete interval computation for depth 13, residue 1825. -/
theorem bounds_13_1825 : exactInterval 13 1825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1825 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1825) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1825 : oddCount 1825 13 = 6 ∧ acceleratedOrbit 13 1825 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1825 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1825) = 3 ^ 6 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1825.1, data_13_1825.2]

/-- Complete interval computation for depth 13, residue 1826. -/
theorem bounds_13_1826 : exactInterval 13 1826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1826 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1826) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1826 : oddCount 1826 13 = 6 ∧ acceleratedOrbit 13 1826 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1826 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1826) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1826.1, data_13_1826.2]

/-- Complete interval computation for depth 13, residue 1827. -/
theorem bounds_13_1827 : exactInterval 13 1827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1827 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1827) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1827 : oddCount 1827 13 = 6 ∧ acceleratedOrbit 13 1827 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1827 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1827) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1827.1, data_13_1827.2]

/-- Complete interval computation for depth 13, residue 1828. -/
theorem bounds_13_1828 : exactInterval 13 1828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1828 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1828) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1828 : oddCount 1828 13 = 6 ∧ acceleratedOrbit 13 1828 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1828 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1828) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1828.1, data_13_1828.2]

/-- Complete interval computation for depth 13, residue 1829. -/
theorem bounds_13_1829 : exactInterval 13 1829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1829 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1829) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1829 : oddCount 1829 13 = 6 ∧ acceleratedOrbit 13 1829 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1829 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1829) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1829.1, data_13_1829.2]

/-- Complete interval computation for depth 13, residue 1830. -/
theorem bounds_13_1830 : exactInterval 13 1830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1830 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1830) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1830 : oddCount 1830 13 = 6 ∧ acceleratedOrbit 13 1830 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1830 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1830) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1830.1, data_13_1830.2]

/-- Complete interval computation for depth 13, residue 1831. -/
theorem bounds_13_1831 : exactInterval 13 1831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1831 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1831) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1831 : oddCount 1831 13 = 8 ∧ acceleratedOrbit 13 1831 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1831 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1831) = 3 ^ 8 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1831.1, data_13_1831.2]

end Collatz.Research.StoppingAtlas.Batch0586
