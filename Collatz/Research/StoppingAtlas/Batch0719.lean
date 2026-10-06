import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0719

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3860. -/
theorem bounds_13_3860 : exactInterval 13 3860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3860 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3860) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3860 : oddCount 3860 13 = 3 ∧ acceleratedOrbit 13 3860 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3860 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3860) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3860.1, data_13_3860.2]

/-- Complete interval computation for depth 13, residue 3861. -/
theorem bounds_13_3861 : exactInterval 13 3861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3861 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3861) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3861 : oddCount 3861 13 = 3 ∧ acceleratedOrbit 13 3861 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3861 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3861) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3861.1, data_13_3861.2]

/-- Complete interval computation for depth 13, residue 3862. -/
theorem bounds_13_3862 : exactInterval 13 3862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3862 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3862) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3862 : oddCount 3862 13 = 8 ∧ acceleratedOrbit 13 3862 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3862 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3862) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3862.1, data_13_3862.2]

/-- Complete interval computation for depth 13, residue 3863. -/
theorem bounds_13_3863 : exactInterval 13 3863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3863 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3863) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3863 : oddCount 3863 13 = 8 ∧ acceleratedOrbit 13 3863 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3863 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3863) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3863.1, data_13_3863.2]

/-- Complete interval computation for depth 13, residue 3864. -/
theorem bounds_13_3864 : exactInterval 13 3864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3864 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3864) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3864 : oddCount 3864 13 = 3 ∧ acceleratedOrbit 13 3864 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3864 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3864) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3864.1, data_13_3864.2]

/-- Complete interval computation for depth 13, residue 3865. -/
theorem bounds_13_3865 : exactInterval 13 3865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3865 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3865) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3865 : oddCount 3865 13 = 8 ∧ acceleratedOrbit 13 3865 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3865 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3865) = 3 ^ 8 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3865.1, data_13_3865.2]

/-- Complete interval computation for depth 13, residue 3866. -/
theorem bounds_13_3866 : exactInterval 13 3866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3866 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3866) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3866 : oddCount 3866 13 = 3 ∧ acceleratedOrbit 13 3866 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3866 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3866) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3866.1, data_13_3866.2]

/-- Complete interval computation for depth 13, residue 3867. -/
theorem bounds_13_3867 : exactInterval 13 3867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3867 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3867) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3867 : oddCount 3867 13 = 10 ∧ acceleratedOrbit 13 3867 = 27884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3867 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3867) = 3 ^ 10 * m + 27884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3867.1, data_13_3867.2]

/-- Complete interval computation for depth 13, residue 3868. -/
theorem bounds_13_3868 : exactInterval 13 3868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3868 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3868) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3868 : oddCount 3868 13 = 8 ∧ acceleratedOrbit 13 3868 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3868 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3868) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3868.1, data_13_3868.2]

/-- Complete interval computation for depth 13, residue 3869. -/
theorem bounds_13_3869 : exactInterval 13 3869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3869 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3869) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3869 : oddCount 3869 13 = 8 ∧ acceleratedOrbit 13 3869 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3869 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3869) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3869.1, data_13_3869.2]

/-- Complete interval computation for depth 13, residue 3870. -/
theorem bounds_13_3870 : exactInterval 13 3870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3870 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3870) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3870 : oddCount 3870 13 = 8 ∧ acceleratedOrbit 13 3870 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3870 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3870) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3870.1, data_13_3870.2]

/-- Complete interval computation for depth 13, residue 3871. -/
theorem bounds_13_3871 : exactInterval 13 3871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3871 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3871) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3871 : oddCount 3871 13 = 9 ∧ acceleratedOrbit 13 3871 = 9305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3871 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3871) = 3 ^ 9 * m + 9305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3871.1, data_13_3871.2]

/-- Complete interval computation for depth 13, residue 3872. -/
theorem bounds_13_3872 : exactInterval 13 3872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3872 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3872) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3872 : oddCount 3872 13 = 6 ∧ acceleratedOrbit 13 3872 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3872 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3872) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3872.1, data_13_3872.2]

/-- Complete interval computation for depth 13, residue 3873. -/
theorem bounds_13_3873 : exactInterval 13 3873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3873 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3873) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3873 : oddCount 3873 13 = 5 ∧ acceleratedOrbit 13 3873 = 115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3873 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3873) = 3 ^ 5 * m + 115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3873.1, data_13_3873.2]

/-- Complete interval computation for depth 13, residue 3874. -/
theorem bounds_13_3874 : exactInterval 13 3874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3874 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3874) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3874 : oddCount 3874 13 = 6 ∧ acceleratedOrbit 13 3874 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3874 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3874) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3874.1, data_13_3874.2]

end Collatz.Research.StoppingAtlas.Batch0719
