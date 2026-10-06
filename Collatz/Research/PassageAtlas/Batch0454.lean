import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0454

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14843. -/
theorem bounds_15_14843 : exactInterval 15 14843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14843 : oddCount 14843 15 = 7 ∧ acceleratedOrbit 15 14843 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14843) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14843.1, data_15_14843.2]

/-- Complete interval computation for depth 15, residue 14844. -/
theorem bounds_15_14844 : exactInterval 15 14844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14844 : oddCount 14844 15 = 12 ∧ acceleratedOrbit 15 14844 = 240812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14844) = 3 ^ 12 * m + 240812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14844.1, data_15_14844.2]

/-- Complete interval computation for depth 15, residue 14845. -/
theorem bounds_15_14845 : exactInterval 15 14845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14845 : oddCount 14845 15 = 12 ∧ acceleratedOrbit 15 14845 = 240812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14845) = 3 ^ 12 * m + 240812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14845.1, data_15_14845.2]

/-- Complete interval computation for depth 15, residue 14846. -/
theorem bounds_15_14846 : exactInterval 15 14846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14846 : oddCount 14846 15 = 12 ∧ acceleratedOrbit 15 14846 = 240812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14846) = 3 ^ 12 * m + 240812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14846.1, data_15_14846.2]

/-- Complete interval computation for depth 15, residue 14847. -/
theorem bounds_15_14847 : exactInterval 15 14847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14847 : oddCount 14847 15 = 13 ∧ acceleratedOrbit 15 14847 = 722429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14847) = 3 ^ 13 * m + 722429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14847.1, data_15_14847.2]

/-- Complete interval computation for depth 15, residue 14848. -/
theorem bounds_15_14848 : exactInterval 15 14848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14848 : oddCount 14848 15 = 3 ∧ acceleratedOrbit 15 14848 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14848) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14848.1, data_15_14848.2]

/-- Complete interval computation for depth 15, residue 14849. -/
theorem bounds_15_14849 : exactInterval 15 14849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14849 : oddCount 14849 15 = 9 ∧ acceleratedOrbit 15 14849 = 8923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14849) = 3 ^ 9 * m + 8923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14849.1, data_15_14849.2]

/-- Complete interval computation for depth 15, residue 14850. -/
theorem bounds_15_14850 : exactInterval 15 14850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14850 : oddCount 14850 15 = 7 ∧ acceleratedOrbit 15 14850 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14850) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14850.1, data_15_14850.2]

/-- Complete interval computation for depth 15, residue 14851. -/
theorem bounds_15_14851 : exactInterval 15 14851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14851 : oddCount 14851 15 = 7 ∧ acceleratedOrbit 15 14851 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14851) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14851.1, data_15_14851.2]

/-- Complete interval computation for depth 15, residue 14852. -/
theorem bounds_15_14852 : exactInterval 15 14852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14852 : oddCount 14852 15 = 9 ∧ acceleratedOrbit 15 14852 = 8930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14852) = 3 ^ 9 * m + 8930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14852.1, data_15_14852.2]

/-- Complete interval computation for depth 15, residue 14853. -/
theorem bounds_15_14853 : exactInterval 15 14853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14853 : oddCount 14853 15 = 9 ∧ acceleratedOrbit 15 14853 = 8930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14853) = 3 ^ 9 * m + 8930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14853.1, data_15_14853.2]

/-- Complete interval computation for depth 15, residue 14854. -/
theorem bounds_15_14854 : exactInterval 15 14854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14854 : oddCount 14854 15 = 9 ∧ acceleratedOrbit 15 14854 = 8930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14854) = 3 ^ 9 * m + 8930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14854.1, data_15_14854.2]

/-- Complete interval computation for depth 15, residue 14855. -/
theorem bounds_15_14855 : exactInterval 15 14855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14855 : oddCount 14855 15 = 8 ∧ acceleratedOrbit 15 14855 = 2975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14855) = 3 ^ 8 * m + 2975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14855.1, data_15_14855.2]

/-- Complete interval computation for depth 15, residue 14856. -/
theorem bounds_15_14856 : exactInterval 15 14856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14856 : oddCount 14856 15 = 4 ∧ acceleratedOrbit 15 14856 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14856) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14856.1, data_15_14856.2]

/-- Complete interval computation for depth 15, residue 14857. -/
theorem bounds_15_14857 : exactInterval 15 14857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14857 : oddCount 14857 15 = 7 ∧ acceleratedOrbit 15 14857 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14857) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14857.1, data_15_14857.2]

/-- Complete interval computation for depth 15, residue 14858. -/
theorem bounds_15_14858 : exactInterval 15 14858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14858 : oddCount 14858 15 = 4 ∧ acceleratedOrbit 15 14858 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14858) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14858.1, data_15_14858.2]

/-- Complete interval computation for depth 15, residue 14859. -/
theorem bounds_15_14859 : exactInterval 15 14859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14859 : oddCount 14859 15 = 9 ∧ acceleratedOrbit 15 14859 = 8930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14859) = 3 ^ 9 * m + 8930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14859.1, data_15_14859.2]

/-- Complete interval computation for depth 15, residue 14860. -/
theorem bounds_15_14860 : exactInterval 15 14860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14860 : oddCount 14860 15 = 4 ∧ acceleratedOrbit 15 14860 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14860) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14860.1, data_15_14860.2]

/-- Complete interval computation for depth 15, residue 14861. -/
theorem bounds_15_14861 : exactInterval 15 14861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14861 : oddCount 14861 15 = 4 ∧ acceleratedOrbit 15 14861 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14861) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14861.1, data_15_14861.2]

/-- Complete interval computation for depth 15, residue 14862. -/
theorem bounds_15_14862 : exactInterval 15 14862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14862 : oddCount 14862 15 = 9 ∧ acceleratedOrbit 15 14862 = 8930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14862) = 3 ^ 9 * m + 8930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14862.1, data_15_14862.2]

/-- Complete interval computation for depth 15, residue 14863. -/
theorem bounds_15_14863 : exactInterval 15 14863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14863 : oddCount 14863 15 = 9 ∧ acceleratedOrbit 15 14863 = 8930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14863) = 3 ^ 9 * m + 8930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14863.1, data_15_14863.2]

/-- Complete interval computation for depth 15, residue 14864. -/
theorem bounds_15_14864 : exactInterval 15 14864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14864 : oddCount 14864 15 = 6 ∧ acceleratedOrbit 15 14864 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14864) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14864.1, data_15_14864.2]

/-- Complete interval computation for depth 15, residue 14865. -/
theorem bounds_15_14865 : exactInterval 15 14865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14865 : oddCount 14865 15 = 4 ∧ acceleratedOrbit 15 14865 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14865) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14865.1, data_15_14865.2]

/-- Complete interval computation for depth 15, residue 14866. -/
theorem bounds_15_14866 : exactInterval 15 14866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14866 : oddCount 14866 15 = 8 ∧ acceleratedOrbit 15 14866 = 2978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14866) = 3 ^ 8 * m + 2978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14866.1, data_15_14866.2]

/-- Complete interval computation for depth 15, residue 14867. -/
theorem bounds_15_14867 : exactInterval 15 14867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14867 : oddCount 14867 15 = 8 ∧ acceleratedOrbit 15 14867 = 2978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14867) = 3 ^ 8 * m + 2978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14867.1, data_15_14867.2]

/-- Complete interval computation for depth 15, residue 14868. -/
theorem bounds_15_14868 : exactInterval 15 14868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14868 : oddCount 14868 15 = 6 ∧ acceleratedOrbit 15 14868 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14868) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14868.1, data_15_14868.2]

/-- Complete interval computation for depth 15, residue 14869. -/
theorem bounds_15_14869 : exactInterval 15 14869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14869 : oddCount 14869 15 = 6 ∧ acceleratedOrbit 15 14869 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14869) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14869.1, data_15_14869.2]

/-- Complete interval computation for depth 15, residue 14870. -/
theorem bounds_15_14870 : exactInterval 15 14870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14870 : oddCount 14870 15 = 6 ∧ acceleratedOrbit 15 14870 = 331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14870) = 3 ^ 6 * m + 331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14870.1, data_15_14870.2]

/-- Complete interval computation for depth 15, residue 14871. -/
theorem bounds_15_14871 : exactInterval 15 14871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14871 : oddCount 14871 15 = 6 ∧ acceleratedOrbit 15 14871 = 331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14871) = 3 ^ 6 * m + 331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14871.1, data_15_14871.2]

/-- Complete interval computation for depth 15, residue 14872. -/
theorem bounds_15_14872 : exactInterval 15 14872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14872 : oddCount 14872 15 = 6 ∧ acceleratedOrbit 15 14872 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14872) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14872.1, data_15_14872.2]

/-- Complete interval computation for depth 15, residue 14873. -/
theorem bounds_15_14873 : exactInterval 15 14873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14873 : oddCount 14873 15 = 6 ∧ acceleratedOrbit 15 14873 = 331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14873) = 3 ^ 6 * m + 331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14873.1, data_15_14873.2]

/-- Complete interval computation for depth 15, residue 14874. -/
theorem bounds_15_14874 : exactInterval 15 14874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14874 : oddCount 14874 15 = 6 ∧ acceleratedOrbit 15 14874 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14874) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14874.1, data_15_14874.2]

/-- Complete interval computation for depth 15, residue 14875. -/
theorem bounds_15_14875 : exactInterval 15 14875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14875 : oddCount 14875 15 = 10 ∧ acceleratedOrbit 15 14875 = 26810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14875) = 3 ^ 10 * m + 26810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14875.1, data_15_14875.2]

end Collatz.Research.PassageAtlas.Batch0454
