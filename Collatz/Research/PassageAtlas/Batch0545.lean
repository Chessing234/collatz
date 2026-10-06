import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0545

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17825. -/
theorem bounds_15_17825 : exactInterval 15 17825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17825 : oddCount 17825 15 = 7 ∧ acceleratedOrbit 15 17825 = 1190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17825) = 3 ^ 7 * m + 1190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17825.1, data_15_17825.2]

/-- Complete interval computation for depth 15, residue 17826. -/
theorem bounds_15_17826 : exactInterval 15 17826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17826 : oddCount 17826 15 = 6 ∧ acceleratedOrbit 15 17826 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17826) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17826.1, data_15_17826.2]

/-- Complete interval computation for depth 15, residue 17827. -/
theorem bounds_15_17827 : exactInterval 15 17827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17827 : oddCount 17827 15 = 6 ∧ acceleratedOrbit 15 17827 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17827) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17827.1, data_15_17827.2]

/-- Complete interval computation for depth 15, residue 17828. -/
theorem bounds_15_17828 : exactInterval 15 17828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17828 : oddCount 17828 15 = 6 ∧ acceleratedOrbit 15 17828 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17828) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17828.1, data_15_17828.2]

/-- Complete interval computation for depth 15, residue 17829. -/
theorem bounds_15_17829 : exactInterval 15 17829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17829 : oddCount 17829 15 = 6 ∧ acceleratedOrbit 15 17829 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17829) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17829.1, data_15_17829.2]

/-- Complete interval computation for depth 15, residue 17830. -/
theorem bounds_15_17830 : exactInterval 15 17830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17830 : oddCount 17830 15 = 6 ∧ acceleratedOrbit 15 17830 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17830) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17830.1, data_15_17830.2]

/-- Complete interval computation for depth 15, residue 17831. -/
theorem bounds_15_17831 : exactInterval 15 17831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17831 : oddCount 17831 15 = 9 ∧ acceleratedOrbit 15 17831 = 10712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17831) = 3 ^ 9 * m + 10712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17831.1, data_15_17831.2]

/-- Complete interval computation for depth 15, residue 17832. -/
theorem bounds_15_17832 : exactInterval 15 17832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17832 : oddCount 17832 15 = 5 ∧ acceleratedOrbit 15 17832 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17832) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17832.1, data_15_17832.2]

/-- Complete interval computation for depth 15, residue 17833. -/
theorem bounds_15_17833 : exactInterval 15 17833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17833 : oddCount 17833 15 = 8 ∧ acceleratedOrbit 15 17833 = 3571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17833) = 3 ^ 8 * m + 3571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17833.1, data_15_17833.2]

/-- Complete interval computation for depth 15, residue 17834. -/
theorem bounds_15_17834 : exactInterval 15 17834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17834 : oddCount 17834 15 = 5 ∧ acceleratedOrbit 15 17834 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17834) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17834.1, data_15_17834.2]

/-- Complete interval computation for depth 15, residue 17835. -/
theorem bounds_15_17835 : exactInterval 15 17835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17835 : oddCount 17835 15 = 8 ∧ acceleratedOrbit 15 17835 = 3572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17835) = 3 ^ 8 * m + 3572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17835.1, data_15_17835.2]

/-- Complete interval computation for depth 15, residue 17836. -/
theorem bounds_15_17836 : exactInterval 15 17836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17836 : oddCount 17836 15 = 6 ∧ acceleratedOrbit 15 17836 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17836) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17836.1, data_15_17836.2]

/-- Complete interval computation for depth 15, residue 17837. -/
theorem bounds_15_17837 : exactInterval 15 17837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17837 : oddCount 17837 15 = 6 ∧ acceleratedOrbit 15 17837 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17837) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17837.1, data_15_17837.2]

/-- Complete interval computation for depth 15, residue 17838. -/
theorem bounds_15_17838 : exactInterval 15 17838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17838 : oddCount 17838 15 = 6 ∧ acceleratedOrbit 15 17838 = 397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17838) = 3 ^ 6 * m + 397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17838.1, data_15_17838.2]

/-- Complete interval computation for depth 15, residue 17839. -/
theorem bounds_15_17839 : exactInterval 15 17839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17839 : oddCount 17839 15 = 9 ∧ acceleratedOrbit 15 17839 = 10718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17839) = 3 ^ 9 * m + 10718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17839.1, data_15_17839.2]

/-- Complete interval computation for depth 15, residue 17840. -/
theorem bounds_15_17840 : exactInterval 15 17840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17840 : oddCount 17840 15 = 8 ∧ acceleratedOrbit 15 17840 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17840) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17840.1, data_15_17840.2]

/-- Complete interval computation for depth 15, residue 17841. -/
theorem bounds_15_17841 : exactInterval 15 17841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17841 : oddCount 17841 15 = 6 ∧ acceleratedOrbit 15 17841 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17841) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17841.1, data_15_17841.2]

/-- Complete interval computation for depth 15, residue 17842. -/
theorem bounds_15_17842 : exactInterval 15 17842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17842 : oddCount 17842 15 = 6 ∧ acceleratedOrbit 15 17842 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17842) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17842.1, data_15_17842.2]

/-- Complete interval computation for depth 15, residue 17843. -/
theorem bounds_15_17843 : exactInterval 15 17843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17843 : oddCount 17843 15 = 6 ∧ acceleratedOrbit 15 17843 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17843) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17843.1, data_15_17843.2]

/-- Complete interval computation for depth 15, residue 17844. -/
theorem bounds_15_17844 : exactInterval 15 17844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17844 : oddCount 17844 15 = 8 ∧ acceleratedOrbit 15 17844 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17844) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17844.1, data_15_17844.2]

/-- Complete interval computation for depth 15, residue 17845. -/
theorem bounds_15_17845 : exactInterval 15 17845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17845 : oddCount 17845 15 = 8 ∧ acceleratedOrbit 15 17845 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17845) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17845.1, data_15_17845.2]

/-- Complete interval computation for depth 15, residue 17846. -/
theorem bounds_15_17846 : exactInterval 15 17846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17846 : oddCount 17846 15 = 8 ∧ acceleratedOrbit 15 17846 = 3574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17846) = 3 ^ 8 * m + 3574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17846.1, data_15_17846.2]

/-- Complete interval computation for depth 15, residue 17847. -/
theorem bounds_15_17847 : exactInterval 15 17847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17847 : oddCount 17847 15 = 8 ∧ acceleratedOrbit 15 17847 = 3574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17847) = 3 ^ 8 * m + 3574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17847.1, data_15_17847.2]

/-- Complete interval computation for depth 15, residue 17848. -/
theorem bounds_15_17848 : exactInterval 15 17848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17848 : oddCount 17848 15 = 8 ∧ acceleratedOrbit 15 17848 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17848) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17848.1, data_15_17848.2]

/-- Complete interval computation for depth 15, residue 17849. -/
theorem bounds_15_17849 : exactInterval 15 17849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17849 : oddCount 17849 15 = 6 ∧ acceleratedOrbit 15 17849 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17849) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17849.1, data_15_17849.2]

/-- Complete interval computation for depth 15, residue 17850. -/
theorem bounds_15_17850 : exactInterval 15 17850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17850 : oddCount 17850 15 = 8 ∧ acceleratedOrbit 15 17850 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17850) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17850.1, data_15_17850.2]

/-- Complete interval computation for depth 15, residue 17851. -/
theorem bounds_15_17851 : exactInterval 15 17851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17851 : oddCount 17851 15 = 8 ∧ acceleratedOrbit 15 17851 = 3575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17851) = 3 ^ 8 * m + 3575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17851.1, data_15_17851.2]

/-- Complete interval computation for depth 15, residue 17852. -/
theorem bounds_15_17852 : exactInterval 15 17852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17852 : oddCount 17852 15 = 7 ∧ acceleratedOrbit 15 17852 = 1192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17852) = 3 ^ 7 * m + 1192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17852.1, data_15_17852.2]

/-- Complete interval computation for depth 15, residue 17853. -/
theorem bounds_15_17853 : exactInterval 15 17853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17853 : oddCount 17853 15 = 7 ∧ acceleratedOrbit 15 17853 = 1192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17853) = 3 ^ 7 * m + 1192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17853.1, data_15_17853.2]

/-- Complete interval computation for depth 15, residue 17854. -/
theorem bounds_15_17854 : exactInterval 15 17854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17854 : oddCount 17854 15 = 7 ∧ acceleratedOrbit 15 17854 = 1192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17854) = 3 ^ 7 * m + 1192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17854.1, data_15_17854.2]

/-- Complete interval computation for depth 15, residue 17855. -/
theorem bounds_15_17855 : exactInterval 15 17855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17855 : oddCount 17855 15 = 12 ∧ acceleratedOrbit 15 17855 = 289595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17855) = 3 ^ 12 * m + 289595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17855.1, data_15_17855.2]

/-- Complete interval computation for depth 15, residue 17856. -/
theorem bounds_15_17856 : exactInterval 15 17856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17856 : oddCount 17856 15 = 5 ∧ acceleratedOrbit 15 17856 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17856) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17856.1, data_15_17856.2]

/-- Complete interval computation for depth 15, residue 17857. -/
theorem bounds_15_17857 : exactInterval 15 17857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17857 : oddCount 17857 15 = 8 ∧ acceleratedOrbit 15 17857 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17857) = 3 ^ 8 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17857.1, data_15_17857.2]

end Collatz.Research.PassageAtlas.Batch0545
