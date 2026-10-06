import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0698

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22839. -/
theorem bounds_15_22839 : exactInterval 15 22839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22839 : oddCount 22839 15 = 10 ∧ acceleratedOrbit 15 22839 = 41161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22839) = 3 ^ 10 * m + 41161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22839.1, data_15_22839.2]

/-- Complete interval computation for depth 15, residue 22840. -/
theorem bounds_15_22840 : exactInterval 15 22840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22840 : oddCount 22840 15 = 8 ∧ acceleratedOrbit 15 22840 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22840) = 3 ^ 8 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22840.1, data_15_22840.2]

/-- Complete interval computation for depth 15, residue 22841. -/
theorem bounds_15_22841 : exactInterval 15 22841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22841 : oddCount 22841 15 = 8 ∧ acceleratedOrbit 15 22841 = 4574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22841) = 3 ^ 8 * m + 4574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22841.1, data_15_22841.2]

/-- Complete interval computation for depth 15, residue 22842. -/
theorem bounds_15_22842 : exactInterval 15 22842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22842 : oddCount 22842 15 = 8 ∧ acceleratedOrbit 15 22842 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22842) = 3 ^ 8 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22842.1, data_15_22842.2]

/-- Complete interval computation for depth 15, residue 22843. -/
theorem bounds_15_22843 : exactInterval 15 22843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22843 : oddCount 22843 15 = 8 ∧ acceleratedOrbit 15 22843 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22843) = 3 ^ 8 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22843.1, data_15_22843.2]

/-- Complete interval computation for depth 15, residue 22844. -/
theorem bounds_15_22844 : exactInterval 15 22844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22844 : oddCount 22844 15 = 8 ∧ acceleratedOrbit 15 22844 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22844) = 3 ^ 8 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22844.1, data_15_22844.2]

/-- Complete interval computation for depth 15, residue 22845. -/
theorem bounds_15_22845 : exactInterval 15 22845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22845 : oddCount 22845 15 = 8 ∧ acceleratedOrbit 15 22845 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22845) = 3 ^ 8 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22845.1, data_15_22845.2]

/-- Complete interval computation for depth 15, residue 22846. -/
theorem bounds_15_22846 : exactInterval 15 22846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22846 : oddCount 22846 15 = 11 ∧ acceleratedOrbit 15 22846 = 123520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22846) = 3 ^ 11 * m + 123520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22846.1, data_15_22846.2]

/-- Complete interval computation for depth 15, residue 22847. -/
theorem bounds_15_22847 : exactInterval 15 22847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22847 : oddCount 22847 15 = 11 ∧ acceleratedOrbit 15 22847 = 123520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22847) = 3 ^ 11 * m + 123520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22847.1, data_15_22847.2]

/-- Complete interval computation for depth 15, residue 22848. -/
theorem bounds_15_22848 : exactInterval 15 22848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22848 : oddCount 22848 15 = 3 ∧ acceleratedOrbit 15 22848 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22848) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22848.1, data_15_22848.2]

/-- Complete interval computation for depth 15, residue 22849. -/
theorem bounds_15_22849 : exactInterval 15 22849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22849 : oddCount 22849 15 = 5 ∧ acceleratedOrbit 15 22849 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22849) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22849.1, data_15_22849.2]

/-- Complete interval computation for depth 15, residue 22850. -/
theorem bounds_15_22850 : exactInterval 15 22850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22850 : oddCount 22850 15 = 10 ∧ acceleratedOrbit 15 22850 = 41188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22850) = 3 ^ 10 * m + 41188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22850.1, data_15_22850.2]

/-- Complete interval computation for depth 15, residue 22851. -/
theorem bounds_15_22851 : exactInterval 15 22851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22851 : oddCount 22851 15 = 10 ∧ acceleratedOrbit 15 22851 = 41188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22851) = 3 ^ 10 * m + 41188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22851.1, data_15_22851.2]

/-- Complete interval computation for depth 15, residue 22852. -/
theorem bounds_15_22852 : exactInterval 15 22852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22852 : oddCount 22852 15 = 8 ∧ acceleratedOrbit 15 22852 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22852) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22852.1, data_15_22852.2]

/-- Complete interval computation for depth 15, residue 22853. -/
theorem bounds_15_22853 : exactInterval 15 22853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22853 : oddCount 22853 15 = 8 ∧ acceleratedOrbit 15 22853 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22853) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22853.1, data_15_22853.2]

/-- Complete interval computation for depth 15, residue 22854. -/
theorem bounds_15_22854 : exactInterval 15 22854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22854 : oddCount 22854 15 = 8 ∧ acceleratedOrbit 15 22854 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22854) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22854.1, data_15_22854.2]

/-- Complete interval computation for depth 15, residue 22855. -/
theorem bounds_15_22855 : exactInterval 15 22855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22855 : oddCount 22855 15 = 12 ∧ acceleratedOrbit 15 22855 = 370696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22855) = 3 ^ 12 * m + 370696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22855.1, data_15_22855.2]

/-- Complete interval computation for depth 15, residue 22856. -/
theorem bounds_15_22856 : exactInterval 15 22856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22856 : oddCount 22856 15 = 8 ∧ acceleratedOrbit 15 22856 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22856) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22856.1, data_15_22856.2]

/-- Complete interval computation for depth 15, residue 22857. -/
theorem bounds_15_22857 : exactInterval 15 22857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22857 : oddCount 22857 15 = 9 ∧ acceleratedOrbit 15 22857 = 13733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22857) = 3 ^ 9 * m + 13733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22857.1, data_15_22857.2]

/-- Complete interval computation for depth 15, residue 22858. -/
theorem bounds_15_22858 : exactInterval 15 22858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22858 : oddCount 22858 15 = 8 ∧ acceleratedOrbit 15 22858 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22858) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22858.1, data_15_22858.2]

/-- Complete interval computation for depth 15, residue 22859. -/
theorem bounds_15_22859 : exactInterval 15 22859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22859 : oddCount 22859 15 = 8 ∧ acceleratedOrbit 15 22859 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22859) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22859.1, data_15_22859.2]

/-- Complete interval computation for depth 15, residue 22860. -/
theorem bounds_15_22860 : exactInterval 15 22860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22860 : oddCount 22860 15 = 8 ∧ acceleratedOrbit 15 22860 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22860) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22860.1, data_15_22860.2]

/-- Complete interval computation for depth 15, residue 22861. -/
theorem bounds_15_22861 : exactInterval 15 22861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22861 : oddCount 22861 15 = 8 ∧ acceleratedOrbit 15 22861 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22861) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22861.1, data_15_22861.2]

/-- Complete interval computation for depth 15, residue 22862. -/
theorem bounds_15_22862 : exactInterval 15 22862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22862 : oddCount 22862 15 = 10 ∧ acceleratedOrbit 15 22862 = 41204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22862) = 3 ^ 10 * m + 41204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22862.1, data_15_22862.2]

/-- Complete interval computation for depth 15, residue 22863. -/
theorem bounds_15_22863 : exactInterval 15 22863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22863 : oddCount 22863 15 = 10 ∧ acceleratedOrbit 15 22863 = 41204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22863) = 3 ^ 10 * m + 41204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22863.1, data_15_22863.2]

/-- Complete interval computation for depth 15, residue 22864. -/
theorem bounds_15_22864 : exactInterval 15 22864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22864 : oddCount 22864 15 = 3 ∧ acceleratedOrbit 15 22864 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22864) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22864.1, data_15_22864.2]

/-- Complete interval computation for depth 15, residue 22865. -/
theorem bounds_15_22865 : exactInterval 15 22865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22865 : oddCount 22865 15 = 8 ∧ acceleratedOrbit 15 22865 = 4579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22865) = 3 ^ 8 * m + 4579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22865.1, data_15_22865.2]

/-- Complete interval computation for depth 15, residue 22866. -/
theorem bounds_15_22866 : exactInterval 15 22866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22866 : oddCount 22866 15 = 8 ∧ acceleratedOrbit 15 22866 = 4579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22866) = 3 ^ 8 * m + 4579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22866.1, data_15_22866.2]

/-- Complete interval computation for depth 15, residue 22867. -/
theorem bounds_15_22867 : exactInterval 15 22867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22867 : oddCount 22867 15 = 8 ∧ acceleratedOrbit 15 22867 = 4579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22867) = 3 ^ 8 * m + 4579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22867.1, data_15_22867.2]

/-- Complete interval computation for depth 15, residue 22868. -/
theorem bounds_15_22868 : exactInterval 15 22868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22868 : oddCount 22868 15 = 3 ∧ acceleratedOrbit 15 22868 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22868) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22868.1, data_15_22868.2]

/-- Complete interval computation for depth 15, residue 22869. -/
theorem bounds_15_22869 : exactInterval 15 22869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22869 : oddCount 22869 15 = 3 ∧ acceleratedOrbit 15 22869 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22869) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22869.1, data_15_22869.2]

/-- Complete interval computation for depth 15, residue 22870. -/
theorem bounds_15_22870 : exactInterval 15 22870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22870 : oddCount 22870 15 = 6 ∧ acceleratedOrbit 15 22870 = 509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22870) = 3 ^ 6 * m + 509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22870.1, data_15_22870.2]

/-- Complete interval computation for depth 15, residue 22871. -/
theorem bounds_15_22871 : exactInterval 15 22871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22871 : oddCount 22871 15 = 6 ∧ acceleratedOrbit 15 22871 = 509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22871) = 3 ^ 6 * m + 509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22871.1, data_15_22871.2]

end Collatz.Research.PassageAtlas.Batch0698
