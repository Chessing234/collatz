import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0484

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15826. -/
theorem bounds_15_15826 : exactInterval 15 15826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15826 : oddCount 15826 15 = 8 ∧ acceleratedOrbit 15 15826 = 3170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15826) = 3 ^ 8 * m + 3170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15826.1, data_15_15826.2]

/-- Complete interval computation for depth 15, residue 15827. -/
theorem bounds_15_15827 : exactInterval 15 15827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15827 : oddCount 15827 15 = 8 ∧ acceleratedOrbit 15 15827 = 3170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15827) = 3 ^ 8 * m + 3170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15827.1, data_15_15827.2]

/-- Complete interval computation for depth 15, residue 15828. -/
theorem bounds_15_15828 : exactInterval 15 15828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15828 : oddCount 15828 15 = 5 ∧ acceleratedOrbit 15 15828 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15828) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15828.1, data_15_15828.2]

/-- Complete interval computation for depth 15, residue 15829. -/
theorem bounds_15_15829 : exactInterval 15 15829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15829 : oddCount 15829 15 = 5 ∧ acceleratedOrbit 15 15829 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15829) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15829.1, data_15_15829.2]

/-- Complete interval computation for depth 15, residue 15830. -/
theorem bounds_15_15830 : exactInterval 15 15830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15830 : oddCount 15830 15 = 7 ∧ acceleratedOrbit 15 15830 = 1057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15830) = 3 ^ 7 * m + 1057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15830.1, data_15_15830.2]

/-- Complete interval computation for depth 15, residue 15831. -/
theorem bounds_15_15831 : exactInterval 15 15831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15831 : oddCount 15831 15 = 7 ∧ acceleratedOrbit 15 15831 = 1057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15831) = 3 ^ 7 * m + 1057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15831.1, data_15_15831.2]

/-- Complete interval computation for depth 15, residue 15832. -/
theorem bounds_15_15832 : exactInterval 15 15832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15832 : oddCount 15832 15 = 6 ∧ acceleratedOrbit 15 15832 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15832) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15832.1, data_15_15832.2]

/-- Complete interval computation for depth 15, residue 15833. -/
theorem bounds_15_15833 : exactInterval 15 15833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15833 : oddCount 15833 15 = 6 ∧ acceleratedOrbit 15 15833 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15833) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15833.1, data_15_15833.2]

/-- Complete interval computation for depth 15, residue 15834. -/
theorem bounds_15_15834 : exactInterval 15 15834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15834 : oddCount 15834 15 = 6 ∧ acceleratedOrbit 15 15834 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15834) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15834.1, data_15_15834.2]

/-- Complete interval computation for depth 15, residue 15835. -/
theorem bounds_15_15835 : exactInterval 15 15835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15835 : oddCount 15835 15 = 8 ∧ acceleratedOrbit 15 15835 = 3172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15835) = 3 ^ 8 * m + 3172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15835.1, data_15_15835.2]

/-- Complete interval computation for depth 15, residue 15836. -/
theorem bounds_15_15836 : exactInterval 15 15836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15836 : oddCount 15836 15 = 6 ∧ acceleratedOrbit 15 15836 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15836) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15836.1, data_15_15836.2]

/-- Complete interval computation for depth 15, residue 15837. -/
theorem bounds_15_15837 : exactInterval 15 15837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15837 : oddCount 15837 15 = 6 ∧ acceleratedOrbit 15 15837 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15837) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15837.1, data_15_15837.2]

/-- Complete interval computation for depth 15, residue 15838. -/
theorem bounds_15_15838 : exactInterval 15 15838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15838 : oddCount 15838 15 = 9 ∧ acceleratedOrbit 15 15838 = 9515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15838) = 3 ^ 9 * m + 9515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15838.1, data_15_15838.2]

/-- Complete interval computation for depth 15, residue 15839. -/
theorem bounds_15_15839 : exactInterval 15 15839 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15839) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15839 : oddCount 15839 15 = 9 ∧ acceleratedOrbit 15 15839 = 9515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15839) = 3 ^ 9 * m + 9515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15839.1, data_15_15839.2]

/-- Complete interval computation for depth 15, residue 15840. -/
theorem bounds_15_15840 : exactInterval 15 15840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15840 : oddCount 15840 15 = 8 ∧ acceleratedOrbit 15 15840 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15840) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15840.1, data_15_15840.2]

/-- Complete interval computation for depth 15, residue 15841. -/
theorem bounds_15_15841 : exactInterval 15 15841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15841 : oddCount 15841 15 = 10 ∧ acceleratedOrbit 15 15841 = 28552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15841) = 3 ^ 10 * m + 28552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15841.1, data_15_15841.2]

/-- Complete interval computation for depth 15, residue 15842. -/
theorem bounds_15_15842 : exactInterval 15 15842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15842 : oddCount 15842 15 = 5 ∧ acceleratedOrbit 15 15842 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15842) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15842.1, data_15_15842.2]

/-- Complete interval computation for depth 15, residue 15843. -/
theorem bounds_15_15843 : exactInterval 15 15843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15843 : oddCount 15843 15 = 5 ∧ acceleratedOrbit 15 15843 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15843) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15843.1, data_15_15843.2]

/-- Complete interval computation for depth 15, residue 15844. -/
theorem bounds_15_15844 : exactInterval 15 15844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15844 : oddCount 15844 15 = 7 ∧ acceleratedOrbit 15 15844 = 1058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15844) = 3 ^ 7 * m + 1058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15844.1, data_15_15844.2]

/-- Complete interval computation for depth 15, residue 15845. -/
theorem bounds_15_15845 : exactInterval 15 15845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15845 : oddCount 15845 15 = 7 ∧ acceleratedOrbit 15 15845 = 1058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15845) = 3 ^ 7 * m + 1058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15845.1, data_15_15845.2]

/-- Complete interval computation for depth 15, residue 15846. -/
theorem bounds_15_15846 : exactInterval 15 15846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15846 : oddCount 15846 15 = 7 ∧ acceleratedOrbit 15 15846 = 1058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15846) = 3 ^ 7 * m + 1058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15846.1, data_15_15846.2]

/-- Complete interval computation for depth 15, residue 15847. -/
theorem bounds_15_15847 : exactInterval 15 15847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15847 : oddCount 15847 15 = 9 ∧ acceleratedOrbit 15 15847 = 9521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15847) = 3 ^ 9 * m + 9521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15847.1, data_15_15847.2]

/-- Complete interval computation for depth 15, residue 15848. -/
theorem bounds_15_15848 : exactInterval 15 15848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15848 : oddCount 15848 15 = 8 ∧ acceleratedOrbit 15 15848 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15848) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15848.1, data_15_15848.2]

/-- Complete interval computation for depth 15, residue 15849. -/
theorem bounds_15_15849 : exactInterval 15 15849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15849 : oddCount 15849 15 = 10 ∧ acceleratedOrbit 15 15849 = 28565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15849) = 3 ^ 10 * m + 28565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15849.1, data_15_15849.2]

/-- Complete interval computation for depth 15, residue 15850. -/
theorem bounds_15_15850 : exactInterval 15 15850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15850 : oddCount 15850 15 = 8 ∧ acceleratedOrbit 15 15850 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15850) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15850.1, data_15_15850.2]

/-- Complete interval computation for depth 15, residue 15851. -/
theorem bounds_15_15851 : exactInterval 15 15851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15851 : oddCount 15851 15 = 10 ∧ acceleratedOrbit 15 15851 = 28568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15851) = 3 ^ 10 * m + 28568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15851.1, data_15_15851.2]

/-- Complete interval computation for depth 15, residue 15852. -/
theorem bounds_15_15852 : exactInterval 15 15852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15852 : oddCount 15852 15 = 8 ∧ acceleratedOrbit 15 15852 = 3176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15852) = 3 ^ 8 * m + 3176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15852.1, data_15_15852.2]

/-- Complete interval computation for depth 15, residue 15853. -/
theorem bounds_15_15853 : exactInterval 15 15853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15853 : oddCount 15853 15 = 8 ∧ acceleratedOrbit 15 15853 = 3176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15853) = 3 ^ 8 * m + 3176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15853.1, data_15_15853.2]

/-- Complete interval computation for depth 15, residue 15854. -/
theorem bounds_15_15854 : exactInterval 15 15854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15854 : oddCount 15854 15 = 8 ∧ acceleratedOrbit 15 15854 = 3176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15854) = 3 ^ 8 * m + 3176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15854.1, data_15_15854.2]

/-- Complete interval computation for depth 15, residue 15855. -/
theorem bounds_15_15855 : exactInterval 15 15855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15855 : oddCount 15855 15 = 10 ∧ acceleratedOrbit 15 15855 = 28574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15855) = 3 ^ 10 * m + 28574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15855.1, data_15_15855.2]

/-- Complete interval computation for depth 15, residue 15856. -/
theorem bounds_15_15856 : exactInterval 15 15856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15856 : oddCount 15856 15 = 8 ∧ acceleratedOrbit 15 15856 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15856) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15856.1, data_15_15856.2]

/-- Complete interval computation for depth 15, residue 15857. -/
theorem bounds_15_15857 : exactInterval 15 15857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15857 : oddCount 15857 15 = 8 ∧ acceleratedOrbit 15 15857 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15857) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15857.1, data_15_15857.2]

/-- Complete interval computation for depth 15, residue 15858. -/
theorem bounds_15_15858 : exactInterval 15 15858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15858 : oddCount 15858 15 = 6 ∧ acceleratedOrbit 15 15858 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15858) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15858.1, data_15_15858.2]

end Collatz.Research.PassageAtlas.Batch0484
