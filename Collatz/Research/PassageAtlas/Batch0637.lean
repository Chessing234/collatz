import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0637

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20840. -/
theorem bounds_15_20840 : exactInterval 15 20840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20840 : oddCount 20840 15 = 5 ∧ acceleratedOrbit 15 20840 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20840) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20840.1, data_15_20840.2]

/-- Complete interval computation for depth 15, residue 20841. -/
theorem bounds_15_20841 : exactInterval 15 20841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20841 : oddCount 20841 15 = 8 ∧ acceleratedOrbit 15 20841 = 4175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20841) = 3 ^ 8 * m + 4175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20841.1, data_15_20841.2]

/-- Complete interval computation for depth 15, residue 20842. -/
theorem bounds_15_20842 : exactInterval 15 20842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20842 : oddCount 20842 15 = 5 ∧ acceleratedOrbit 15 20842 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20842) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20842.1, data_15_20842.2]

/-- Complete interval computation for depth 15, residue 20843. -/
theorem bounds_15_20843 : exactInterval 15 20843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20843 : oddCount 20843 15 = 8 ∧ acceleratedOrbit 15 20843 = 4175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20843) = 3 ^ 8 * m + 4175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20843.1, data_15_20843.2]

/-- Complete interval computation for depth 15, residue 20844. -/
theorem bounds_15_20844 : exactInterval 15 20844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20844 : oddCount 20844 15 = 10 ∧ acceleratedOrbit 15 20844 = 37574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20844) = 3 ^ 10 * m + 37574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20844.1, data_15_20844.2]

/-- Complete interval computation for depth 15, residue 20845. -/
theorem bounds_15_20845 : exactInterval 15 20845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20845 : oddCount 20845 15 = 10 ∧ acceleratedOrbit 15 20845 = 37574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20845) = 3 ^ 10 * m + 37574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20845.1, data_15_20845.2]

/-- Complete interval computation for depth 15, residue 20846. -/
theorem bounds_15_20846 : exactInterval 15 20846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20846 : oddCount 20846 15 = 10 ∧ acceleratedOrbit 15 20846 = 37574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20846) = 3 ^ 10 * m + 37574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20846.1, data_15_20846.2]

/-- Complete interval computation for depth 15, residue 20847. -/
theorem bounds_15_20847 : exactInterval 15 20847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20847 : oddCount 20847 15 = 8 ∧ acceleratedOrbit 15 20847 = 4175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20847) = 3 ^ 8 * m + 4175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20847.1, data_15_20847.2]

/-- Complete interval computation for depth 15, residue 20848. -/
theorem bounds_15_20848 : exactInterval 15 20848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20848 : oddCount 20848 15 = 5 ∧ acceleratedOrbit 15 20848 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20848) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20848.1, data_15_20848.2]

/-- Complete interval computation for depth 15, residue 20849. -/
theorem bounds_15_20849 : exactInterval 15 20849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20849 : oddCount 20849 15 = 5 ∧ acceleratedOrbit 15 20849 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20849) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20849.1, data_15_20849.2]

/-- Complete interval computation for depth 15, residue 20850. -/
theorem bounds_15_20850 : exactInterval 15 20850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20850 : oddCount 20850 15 = 6 ∧ acceleratedOrbit 15 20850 = 464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20850) = 3 ^ 6 * m + 464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20850.1, data_15_20850.2]

/-- Complete interval computation for depth 15, residue 20851. -/
theorem bounds_15_20851 : exactInterval 15 20851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20851 : oddCount 20851 15 = 6 ∧ acceleratedOrbit 15 20851 = 464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20851) = 3 ^ 6 * m + 464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20851.1, data_15_20851.2]

/-- Complete interval computation for depth 15, residue 20852. -/
theorem bounds_15_20852 : exactInterval 15 20852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20852 : oddCount 20852 15 = 5 ∧ acceleratedOrbit 15 20852 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20852) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20852.1, data_15_20852.2]

/-- Complete interval computation for depth 15, residue 20853. -/
theorem bounds_15_20853 : exactInterval 15 20853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20853 : oddCount 20853 15 = 5 ∧ acceleratedOrbit 15 20853 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20853) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20853.1, data_15_20853.2]

/-- Complete interval computation for depth 15, residue 20854. -/
theorem bounds_15_20854 : exactInterval 15 20854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20854 : oddCount 20854 15 = 9 ∧ acceleratedOrbit 15 20854 = 12530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20854) = 3 ^ 9 * m + 12530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20854.1, data_15_20854.2]

/-- Complete interval computation for depth 15, residue 20855. -/
theorem bounds_15_20855 : exactInterval 15 20855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20855 : oddCount 20855 15 = 9 ∧ acceleratedOrbit 15 20855 = 12530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20855) = 3 ^ 9 * m + 12530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20855.1, data_15_20855.2]

/-- Complete interval computation for depth 15, residue 20856. -/
theorem bounds_15_20856 : exactInterval 15 20856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20856 : oddCount 20856 15 = 8 ∧ acceleratedOrbit 15 20856 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20856) = 3 ^ 8 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20856.1, data_15_20856.2]

/-- Complete interval computation for depth 15, residue 20857. -/
theorem bounds_15_20857 : exactInterval 15 20857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20857 : oddCount 20857 15 = 10 ∧ acceleratedOrbit 15 20857 = 37589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20857) = 3 ^ 10 * m + 37589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20857.1, data_15_20857.2]

/-- Complete interval computation for depth 15, residue 20858. -/
theorem bounds_15_20858 : exactInterval 15 20858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20858 : oddCount 20858 15 = 8 ∧ acceleratedOrbit 15 20858 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20858) = 3 ^ 8 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20858.1, data_15_20858.2]

/-- Complete interval computation for depth 15, residue 20859. -/
theorem bounds_15_20859 : exactInterval 15 20859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20859 : oddCount 20859 15 = 8 ∧ acceleratedOrbit 15 20859 = 4177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20859) = 3 ^ 8 * m + 4177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20859.1, data_15_20859.2]

/-- Complete interval computation for depth 15, residue 20860. -/
theorem bounds_15_20860 : exactInterval 15 20860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20860 : oddCount 20860 15 = 8 ∧ acceleratedOrbit 15 20860 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20860) = 3 ^ 8 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20860.1, data_15_20860.2]

/-- Complete interval computation for depth 15, residue 20861. -/
theorem bounds_15_20861 : exactInterval 15 20861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20861 : oddCount 20861 15 = 8 ∧ acceleratedOrbit 15 20861 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20861) = 3 ^ 8 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20861.1, data_15_20861.2]

/-- Complete interval computation for depth 15, residue 20862. -/
theorem bounds_15_20862 : exactInterval 15 20862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20862 : oddCount 20862 15 = 8 ∧ acceleratedOrbit 15 20862 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20862) = 3 ^ 8 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20862.1, data_15_20862.2]

/-- Complete interval computation for depth 15, residue 20863. -/
theorem bounds_15_20863 : exactInterval 15 20863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20863 : oddCount 20863 15 = 8 ∧ acceleratedOrbit 15 20863 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20863) = 3 ^ 8 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20863.1, data_15_20863.2]

/-- Complete interval computation for depth 15, residue 20864. -/
theorem bounds_15_20864 : exactInterval 15 20864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20864 : oddCount 20864 15 = 4 ∧ acceleratedOrbit 15 20864 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20864) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20864.1, data_15_20864.2]

/-- Complete interval computation for depth 15, residue 20865. -/
theorem bounds_15_20865 : exactInterval 15 20865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20865 : oddCount 20865 15 = 7 ∧ acceleratedOrbit 15 20865 = 1394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20865) = 3 ^ 7 * m + 1394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20865.1, data_15_20865.2]

/-- Complete interval computation for depth 15, residue 20866. -/
theorem bounds_15_20866 : exactInterval 15 20866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20866 : oddCount 20866 15 = 7 ∧ acceleratedOrbit 15 20866 = 1394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20866) = 3 ^ 7 * m + 1394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20866.1, data_15_20866.2]

/-- Complete interval computation for depth 15, residue 20867. -/
theorem bounds_15_20867 : exactInterval 15 20867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20867 : oddCount 20867 15 = 7 ∧ acceleratedOrbit 15 20867 = 1394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20867) = 3 ^ 7 * m + 1394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20867.1, data_15_20867.2]

/-- Complete interval computation for depth 15, residue 20868. -/
theorem bounds_15_20868 : exactInterval 15 20868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20868 : oddCount 20868 15 = 7 ∧ acceleratedOrbit 15 20868 = 1394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20868) = 3 ^ 7 * m + 1394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20868.1, data_15_20868.2]

/-- Complete interval computation for depth 15, residue 20869. -/
theorem bounds_15_20869 : exactInterval 15 20869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20869 : oddCount 20869 15 = 7 ∧ acceleratedOrbit 15 20869 = 1394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20869) = 3 ^ 7 * m + 1394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20869.1, data_15_20869.2]

/-- Complete interval computation for depth 15, residue 20870. -/
theorem bounds_15_20870 : exactInterval 15 20870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20870 : oddCount 20870 15 = 7 ∧ acceleratedOrbit 15 20870 = 1394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20870) = 3 ^ 7 * m + 1394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20870.1, data_15_20870.2]

/-- Complete interval computation for depth 15, residue 20871. -/
theorem bounds_15_20871 : exactInterval 15 20871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20871 : oddCount 20871 15 = 7 ∧ acceleratedOrbit 15 20871 = 1394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20871) = 3 ^ 7 * m + 1394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20871.1, data_15_20871.2]

/-- Complete interval computation for depth 15, residue 20872. -/
theorem bounds_15_20872 : exactInterval 15 20872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20872 : oddCount 20872 15 = 7 ∧ acceleratedOrbit 15 20872 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20872) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20872.1, data_15_20872.2]

end Collatz.Research.PassageAtlas.Batch0637
