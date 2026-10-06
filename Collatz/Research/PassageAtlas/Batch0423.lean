import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0423

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13828. -/
theorem bounds_15_13828 : exactInterval 15 13828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13828 : oddCount 13828 15 = 6 ∧ acceleratedOrbit 15 13828 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13828) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13828.1, data_15_13828.2]

/-- Complete interval computation for depth 15, residue 13829. -/
theorem bounds_15_13829 : exactInterval 15 13829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13829 : oddCount 13829 15 = 6 ∧ acceleratedOrbit 15 13829 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13829) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13829.1, data_15_13829.2]

/-- Complete interval computation for depth 15, residue 13830. -/
theorem bounds_15_13830 : exactInterval 15 13830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13830 : oddCount 13830 15 = 6 ∧ acceleratedOrbit 15 13830 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13830) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13830.1, data_15_13830.2]

/-- Complete interval computation for depth 15, residue 13831. -/
theorem bounds_15_13831 : exactInterval 15 13831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13831 : oddCount 13831 15 = 8 ∧ acceleratedOrbit 15 13831 = 2771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13831) = 3 ^ 8 * m + 2771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13831.1, data_15_13831.2]

/-- Complete interval computation for depth 15, residue 13832. -/
theorem bounds_15_13832 : exactInterval 15 13832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13832 : oddCount 13832 15 = 5 ∧ acceleratedOrbit 15 13832 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13832) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13832.1, data_15_13832.2]

/-- Complete interval computation for depth 15, residue 13833. -/
theorem bounds_15_13833 : exactInterval 15 13833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13833 : oddCount 13833 15 = 8 ∧ acceleratedOrbit 15 13833 = 2771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13833) = 3 ^ 8 * m + 2771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13833.1, data_15_13833.2]

/-- Complete interval computation for depth 15, residue 13834. -/
theorem bounds_15_13834 : exactInterval 15 13834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13834 : oddCount 13834 15 = 5 ∧ acceleratedOrbit 15 13834 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13834) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13834.1, data_15_13834.2]

/-- Complete interval computation for depth 15, residue 13835. -/
theorem bounds_15_13835 : exactInterval 15 13835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13835 : oddCount 13835 15 = 6 ∧ acceleratedOrbit 15 13835 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13835) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13835.1, data_15_13835.2]

/-- Complete interval computation for depth 15, residue 13836. -/
theorem bounds_15_13836 : exactInterval 15 13836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13836 : oddCount 13836 15 = 5 ∧ acceleratedOrbit 15 13836 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13836) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13836.1, data_15_13836.2]

/-- Complete interval computation for depth 15, residue 13837. -/
theorem bounds_15_13837 : exactInterval 15 13837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13837 : oddCount 13837 15 = 5 ∧ acceleratedOrbit 15 13837 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13837) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13837.1, data_15_13837.2]

/-- Complete interval computation for depth 15, residue 13838. -/
theorem bounds_15_13838 : exactInterval 15 13838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13838 : oddCount 13838 15 = 10 ∧ acceleratedOrbit 15 13838 = 24947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13838) = 3 ^ 10 * m + 24947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13838.1, data_15_13838.2]

/-- Complete interval computation for depth 15, residue 13839. -/
theorem bounds_15_13839 : exactInterval 15 13839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13839 : oddCount 13839 15 = 10 ∧ acceleratedOrbit 15 13839 = 24947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13839) = 3 ^ 10 * m + 24947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13839.1, data_15_13839.2]

/-- Complete interval computation for depth 15, residue 13840. -/
theorem bounds_15_13840 : exactInterval 15 13840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13840 : oddCount 13840 15 = 8 ∧ acceleratedOrbit 15 13840 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13840) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13840.1, data_15_13840.2]

/-- Complete interval computation for depth 15, residue 13841. -/
theorem bounds_15_13841 : exactInterval 15 13841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13841 : oddCount 13841 15 = 5 ∧ acceleratedOrbit 15 13841 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13841) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13841.1, data_15_13841.2]

/-- Complete interval computation for depth 15, residue 13842. -/
theorem bounds_15_13842 : exactInterval 15 13842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13842 : oddCount 13842 15 = 9 ∧ acceleratedOrbit 15 13842 = 8318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13842) = 3 ^ 9 * m + 8318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13842.1, data_15_13842.2]

/-- Complete interval computation for depth 15, residue 13843. -/
theorem bounds_15_13843 : exactInterval 15 13843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13843 : oddCount 13843 15 = 9 ∧ acceleratedOrbit 15 13843 = 8318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13843) = 3 ^ 9 * m + 8318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13843.1, data_15_13843.2]

/-- Complete interval computation for depth 15, residue 13844. -/
theorem bounds_15_13844 : exactInterval 15 13844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13844 : oddCount 13844 15 = 8 ∧ acceleratedOrbit 15 13844 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13844) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13844.1, data_15_13844.2]

/-- Complete interval computation for depth 15, residue 13845. -/
theorem bounds_15_13845 : exactInterval 15 13845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13845 : oddCount 13845 15 = 8 ∧ acceleratedOrbit 15 13845 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13845) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13845.1, data_15_13845.2]

/-- Complete interval computation for depth 15, residue 13846. -/
theorem bounds_15_13846 : exactInterval 15 13846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13846 : oddCount 13846 15 = 8 ∧ acceleratedOrbit 15 13846 = 2774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13846) = 3 ^ 8 * m + 2774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13846.1, data_15_13846.2]

/-- Complete interval computation for depth 15, residue 13847. -/
theorem bounds_15_13847 : exactInterval 15 13847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13847 : oddCount 13847 15 = 8 ∧ acceleratedOrbit 15 13847 = 2774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13847) = 3 ^ 8 * m + 2774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13847.1, data_15_13847.2]

/-- Complete interval computation for depth 15, residue 13848. -/
theorem bounds_15_13848 : exactInterval 15 13848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13848 : oddCount 13848 15 = 8 ∧ acceleratedOrbit 15 13848 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13848) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13848.1, data_15_13848.2]

/-- Complete interval computation for depth 15, residue 13849. -/
theorem bounds_15_13849 : exactInterval 15 13849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13849 : oddCount 13849 15 = 8 ∧ acceleratedOrbit 15 13849 = 2774 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13849) = 3 ^ 8 * m + 2774 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13849.1, data_15_13849.2]

/-- Complete interval computation for depth 15, residue 13850. -/
theorem bounds_15_13850 : exactInterval 15 13850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13850 : oddCount 13850 15 = 8 ∧ acceleratedOrbit 15 13850 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13850) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13850.1, data_15_13850.2]

/-- Complete interval computation for depth 15, residue 13851. -/
theorem bounds_15_13851 : exactInterval 15 13851 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13851) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13851 : oddCount 13851 15 = 9 ∧ acceleratedOrbit 15 13851 = 8321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13851) = 3 ^ 9 * m + 8321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13851.1, data_15_13851.2]

/-- Complete interval computation for depth 15, residue 13852. -/
theorem bounds_15_13852 : exactInterval 15 13852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13852 : oddCount 13852 15 = 5 ∧ acceleratedOrbit 15 13852 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13852) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13852.1, data_15_13852.2]

/-- Complete interval computation for depth 15, residue 13853. -/
theorem bounds_15_13853 : exactInterval 15 13853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13853 : oddCount 13853 15 = 5 ∧ acceleratedOrbit 15 13853 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13853) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13853.1, data_15_13853.2]

/-- Complete interval computation for depth 15, residue 13854. -/
theorem bounds_15_13854 : exactInterval 15 13854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13854 : oddCount 13854 15 = 5 ∧ acceleratedOrbit 15 13854 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13854) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13854.1, data_15_13854.2]

/-- Complete interval computation for depth 15, residue 13855. -/
theorem bounds_15_13855 : exactInterval 15 13855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13855 : oddCount 13855 15 = 10 ∧ acceleratedOrbit 15 13855 = 24970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13855) = 3 ^ 10 * m + 24970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13855.1, data_15_13855.2]

/-- Complete interval computation for depth 15, residue 13856. -/
theorem bounds_15_13856 : exactInterval 15 13856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13856 : oddCount 13856 15 = 4 ∧ acceleratedOrbit 15 13856 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13856) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13856.1, data_15_13856.2]

/-- Complete interval computation for depth 15, residue 13857. -/
theorem bounds_15_13857 : exactInterval 15 13857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13857 : oddCount 13857 15 = 8 ∧ acceleratedOrbit 15 13857 = 2776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13857) = 3 ^ 8 * m + 2776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13857.1, data_15_13857.2]

/-- Complete interval computation for depth 15, residue 13858. -/
theorem bounds_15_13858 : exactInterval 15 13858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13858 : oddCount 13858 15 = 8 ∧ acceleratedOrbit 15 13858 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13858) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13858.1, data_15_13858.2]

/-- Complete interval computation for depth 15, residue 13859. -/
theorem bounds_15_13859 : exactInterval 15 13859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13859 : oddCount 13859 15 = 8 ∧ acceleratedOrbit 15 13859 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13859) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13859.1, data_15_13859.2]

end Collatz.Research.PassageAtlas.Batch0423
