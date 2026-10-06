import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0576

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18841. -/
theorem bounds_15_18841 : exactInterval 15 18841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18841 : oddCount 18841 15 = 7 ∧ acceleratedOrbit 15 18841 = 1259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18841) = 3 ^ 7 * m + 1259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18841.1, data_15_18841.2]

/-- Complete interval computation for depth 15, residue 18842. -/
theorem bounds_15_18842 : exactInterval 15 18842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18842 : oddCount 18842 15 = 5 ∧ acceleratedOrbit 15 18842 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18842) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18842.1, data_15_18842.2]

/-- Complete interval computation for depth 15, residue 18843. -/
theorem bounds_15_18843 : exactInterval 15 18843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18843 : oddCount 18843 15 = 10 ∧ acceleratedOrbit 15 18843 = 33959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18843) = 3 ^ 10 * m + 33959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18843.1, data_15_18843.2]

/-- Complete interval computation for depth 15, residue 18844. -/
theorem bounds_15_18844 : exactInterval 15 18844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18844 : oddCount 18844 15 = 7 ∧ acceleratedOrbit 15 18844 = 1258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18844) = 3 ^ 7 * m + 1258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18844.1, data_15_18844.2]

/-- Complete interval computation for depth 15, residue 18845. -/
theorem bounds_15_18845 : exactInterval 15 18845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18845 : oddCount 18845 15 = 7 ∧ acceleratedOrbit 15 18845 = 1258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18845) = 3 ^ 7 * m + 1258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18845.1, data_15_18845.2]

/-- Complete interval computation for depth 15, residue 18846. -/
theorem bounds_15_18846 : exactInterval 15 18846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18846 : oddCount 18846 15 = 7 ∧ acceleratedOrbit 15 18846 = 1258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18846) = 3 ^ 7 * m + 1258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18846.1, data_15_18846.2]

/-- Complete interval computation for depth 15, residue 18847. -/
theorem bounds_15_18847 : exactInterval 15 18847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18847 : oddCount 18847 15 = 11 ∧ acceleratedOrbit 15 18847 = 101897 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18847) = 3 ^ 11 * m + 101897 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18847.1, data_15_18847.2]

/-- Complete interval computation for depth 15, residue 18848. -/
theorem bounds_15_18848 : exactInterval 15 18848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18848 : oddCount 18848 15 = 4 ∧ acceleratedOrbit 15 18848 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18848) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18848.1, data_15_18848.2]

/-- Complete interval computation for depth 15, residue 18849. -/
theorem bounds_15_18849 : exactInterval 15 18849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18849 : oddCount 18849 15 = 8 ∧ acceleratedOrbit 15 18849 = 3775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18849) = 3 ^ 8 * m + 3775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18849.1, data_15_18849.2]

/-- Complete interval computation for depth 15, residue 18850. -/
theorem bounds_15_18850 : exactInterval 15 18850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18850 : oddCount 18850 15 = 9 ∧ acceleratedOrbit 15 18850 = 11330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18850) = 3 ^ 9 * m + 11330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18850.1, data_15_18850.2]

/-- Complete interval computation for depth 15, residue 18851. -/
theorem bounds_15_18851 : exactInterval 15 18851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18851 : oddCount 18851 15 = 9 ∧ acceleratedOrbit 15 18851 = 11330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18851) = 3 ^ 9 * m + 11330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18851.1, data_15_18851.2]

/-- Complete interval computation for depth 15, residue 18852. -/
theorem bounds_15_18852 : exactInterval 15 18852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18852 : oddCount 18852 15 = 9 ∧ acceleratedOrbit 15 18852 = 11330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18852) = 3 ^ 9 * m + 11330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18852.1, data_15_18852.2]

/-- Complete interval computation for depth 15, residue 18853. -/
theorem bounds_15_18853 : exactInterval 15 18853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18853 : oddCount 18853 15 = 9 ∧ acceleratedOrbit 15 18853 = 11330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18853) = 3 ^ 9 * m + 11330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18853.1, data_15_18853.2]

/-- Complete interval computation for depth 15, residue 18854. -/
theorem bounds_15_18854 : exactInterval 15 18854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18854 : oddCount 18854 15 = 9 ∧ acceleratedOrbit 15 18854 = 11330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18854) = 3 ^ 9 * m + 11330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18854.1, data_15_18854.2]

/-- Complete interval computation for depth 15, residue 18855. -/
theorem bounds_15_18855 : exactInterval 15 18855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18855 : oddCount 18855 15 = 7 ∧ acceleratedOrbit 15 18855 = 1259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18855) = 3 ^ 7 * m + 1259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18855.1, data_15_18855.2]

/-- Complete interval computation for depth 15, residue 18856. -/
theorem bounds_15_18856 : exactInterval 15 18856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18856 : oddCount 18856 15 = 4 ∧ acceleratedOrbit 15 18856 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18856) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18856.1, data_15_18856.2]

/-- Complete interval computation for depth 15, residue 18857. -/
theorem bounds_15_18857 : exactInterval 15 18857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18857 : oddCount 18857 15 = 8 ∧ acceleratedOrbit 15 18857 = 3776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18857) = 3 ^ 8 * m + 3776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18857.1, data_15_18857.2]

/-- Complete interval computation for depth 15, residue 18858. -/
theorem bounds_15_18858 : exactInterval 15 18858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18858 : oddCount 18858 15 = 4 ∧ acceleratedOrbit 15 18858 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18858) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18858.1, data_15_18858.2]

/-- Complete interval computation for depth 15, residue 18859. -/
theorem bounds_15_18859 : exactInterval 15 18859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18859 : oddCount 18859 15 = 11 ∧ acceleratedOrbit 15 18859 = 101969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18859) = 3 ^ 11 * m + 101969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18859.1, data_15_18859.2]

/-- Complete interval computation for depth 15, residue 18860. -/
theorem bounds_15_18860 : exactInterval 15 18860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18860 : oddCount 18860 15 = 8 ∧ acceleratedOrbit 15 18860 = 3779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18860) = 3 ^ 8 * m + 3779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18860.1, data_15_18860.2]

/-- Complete interval computation for depth 15, residue 18861. -/
theorem bounds_15_18861 : exactInterval 15 18861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18861 : oddCount 18861 15 = 8 ∧ acceleratedOrbit 15 18861 = 3779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18861) = 3 ^ 8 * m + 3779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18861.1, data_15_18861.2]

/-- Complete interval computation for depth 15, residue 18862. -/
theorem bounds_15_18862 : exactInterval 15 18862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18862 : oddCount 18862 15 = 8 ∧ acceleratedOrbit 15 18862 = 3779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18862) = 3 ^ 8 * m + 3779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18862.1, data_15_18862.2]

/-- Complete interval computation for depth 15, residue 18863. -/
theorem bounds_15_18863 : exactInterval 15 18863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18863 : oddCount 18863 15 = 9 ∧ acceleratedOrbit 15 18863 = 11333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18863) = 3 ^ 9 * m + 11333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18863.1, data_15_18863.2]

/-- Complete interval computation for depth 15, residue 18864. -/
theorem bounds_15_18864 : exactInterval 15 18864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18864 : oddCount 18864 15 = 8 ∧ acceleratedOrbit 15 18864 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18864) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18864.1, data_15_18864.2]

/-- Complete interval computation for depth 15, residue 18865. -/
theorem bounds_15_18865 : exactInterval 15 18865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18865 : oddCount 18865 15 = 5 ∧ acceleratedOrbit 15 18865 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18865) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18865.1, data_15_18865.2]

/-- Complete interval computation for depth 15, residue 18866. -/
theorem bounds_15_18866 : exactInterval 15 18866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18866 : oddCount 18866 15 = 5 ∧ acceleratedOrbit 15 18866 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18866) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18866.1, data_15_18866.2]

/-- Complete interval computation for depth 15, residue 18867. -/
theorem bounds_15_18867 : exactInterval 15 18867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18867 : oddCount 18867 15 = 5 ∧ acceleratedOrbit 15 18867 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18867) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18867.1, data_15_18867.2]

/-- Complete interval computation for depth 15, residue 18868. -/
theorem bounds_15_18868 : exactInterval 15 18868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18868 : oddCount 18868 15 = 8 ∧ acceleratedOrbit 15 18868 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18868) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18868.1, data_15_18868.2]

/-- Complete interval computation for depth 15, residue 18869. -/
theorem bounds_15_18869 : exactInterval 15 18869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18869 : oddCount 18869 15 = 8 ∧ acceleratedOrbit 15 18869 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18869) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18869.1, data_15_18869.2]

/-- Complete interval computation for depth 15, residue 18870. -/
theorem bounds_15_18870 : exactInterval 15 18870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18870 : oddCount 18870 15 = 9 ∧ acceleratedOrbit 15 18870 = 11339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18870) = 3 ^ 9 * m + 11339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18870.1, data_15_18870.2]

/-- Complete interval computation for depth 15, residue 18871. -/
theorem bounds_15_18871 : exactInterval 15 18871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18871 : oddCount 18871 15 = 9 ∧ acceleratedOrbit 15 18871 = 11339 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18871) = 3 ^ 9 * m + 11339 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18871.1, data_15_18871.2]

/-- Complete interval computation for depth 15, residue 18872. -/
theorem bounds_15_18872 : exactInterval 15 18872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18872 : oddCount 18872 15 = 8 ∧ acceleratedOrbit 15 18872 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18872) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18872.1, data_15_18872.2]

/-- Complete interval computation for depth 15, residue 18873. -/
theorem bounds_15_18873 : exactInterval 15 18873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18873 : oddCount 18873 15 = 5 ∧ acceleratedOrbit 15 18873 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18873) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18873.1, data_15_18873.2]

end Collatz.Research.PassageAtlas.Batch0576
