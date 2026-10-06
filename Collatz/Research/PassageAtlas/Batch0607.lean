import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0607

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19857. -/
theorem bounds_15_19857 : exactInterval 15 19857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19857 : oddCount 19857 15 = 6 ∧ acceleratedOrbit 15 19857 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19857) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19857.1, data_15_19857.2]

/-- Complete interval computation for depth 15, residue 19858. -/
theorem bounds_15_19858 : exactInterval 15 19858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19858 : oddCount 19858 15 = 6 ∧ acceleratedOrbit 15 19858 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19858) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19858.1, data_15_19858.2]

/-- Complete interval computation for depth 15, residue 19859. -/
theorem bounds_15_19859 : exactInterval 15 19859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19859 : oddCount 19859 15 = 6 ∧ acceleratedOrbit 15 19859 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19859) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19859.1, data_15_19859.2]

/-- Complete interval computation for depth 15, residue 19860. -/
theorem bounds_15_19860 : exactInterval 15 19860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19860 : oddCount 19860 15 = 5 ∧ acceleratedOrbit 15 19860 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19860) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19860.1, data_15_19860.2]

/-- Complete interval computation for depth 15, residue 19861. -/
theorem bounds_15_19861 : exactInterval 15 19861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19861 : oddCount 19861 15 = 5 ∧ acceleratedOrbit 15 19861 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19861) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19861.1, data_15_19861.2]

/-- Complete interval computation for depth 15, residue 19862. -/
theorem bounds_15_19862 : exactInterval 15 19862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19862 : oddCount 19862 15 = 8 ∧ acceleratedOrbit 15 19862 = 3979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19862) = 3 ^ 8 * m + 3979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19862.1, data_15_19862.2]

/-- Complete interval computation for depth 15, residue 19863. -/
theorem bounds_15_19863 : exactInterval 15 19863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19863 : oddCount 19863 15 = 8 ∧ acceleratedOrbit 15 19863 = 3979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19863) = 3 ^ 8 * m + 3979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19863.1, data_15_19863.2]

/-- Complete interval computation for depth 15, residue 19864. -/
theorem bounds_15_19864 : exactInterval 15 19864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19864 : oddCount 19864 15 = 5 ∧ acceleratedOrbit 15 19864 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19864) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19864.1, data_15_19864.2]

/-- Complete interval computation for depth 15, residue 19865. -/
theorem bounds_15_19865 : exactInterval 15 19865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19865 : oddCount 19865 15 = 8 ∧ acceleratedOrbit 15 19865 = 3979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19865) = 3 ^ 8 * m + 3979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19865.1, data_15_19865.2]

/-- Complete interval computation for depth 15, residue 19866. -/
theorem bounds_15_19866 : exactInterval 15 19866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19866 : oddCount 19866 15 = 5 ∧ acceleratedOrbit 15 19866 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19866) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19866.1, data_15_19866.2]

/-- Complete interval computation for depth 15, residue 19867. -/
theorem bounds_15_19867 : exactInterval 15 19867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19867 : oddCount 19867 15 = 9 ∧ acceleratedOrbit 15 19867 = 11935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19867) = 3 ^ 9 * m + 11935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19867.1, data_15_19867.2]

/-- Complete interval computation for depth 15, residue 19868. -/
theorem bounds_15_19868 : exactInterval 15 19868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19868 : oddCount 19868 15 = 10 ∧ acceleratedOrbit 15 19868 = 35812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19868) = 3 ^ 10 * m + 35812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19868.1, data_15_19868.2]

/-- Complete interval computation for depth 15, residue 19869. -/
theorem bounds_15_19869 : exactInterval 15 19869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19869 : oddCount 19869 15 = 10 ∧ acceleratedOrbit 15 19869 = 35812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19869) = 3 ^ 10 * m + 35812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19869.1, data_15_19869.2]

/-- Complete interval computation for depth 15, residue 19870. -/
theorem bounds_15_19870 : exactInterval 15 19870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19870 : oddCount 19870 15 = 10 ∧ acceleratedOrbit 15 19870 = 35812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19870) = 3 ^ 10 * m + 35812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19870.1, data_15_19870.2]

/-- Complete interval computation for depth 15, residue 19871. -/
theorem bounds_15_19871 : exactInterval 15 19871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19871 : oddCount 19871 15 = 11 ∧ acceleratedOrbit 15 19871 = 107432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19871) = 3 ^ 11 * m + 107432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19871.1, data_15_19871.2]

/-- Complete interval computation for depth 15, residue 19872. -/
theorem bounds_15_19872 : exactInterval 15 19872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19872 : oddCount 19872 15 = 6 ∧ acceleratedOrbit 15 19872 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19872) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19872.1, data_15_19872.2]

/-- Complete interval computation for depth 15, residue 19873. -/
theorem bounds_15_19873 : exactInterval 15 19873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19873 : oddCount 19873 15 = 8 ∧ acceleratedOrbit 15 19873 = 3980 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19873) = 3 ^ 8 * m + 3980 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19873.1, data_15_19873.2]

/-- Complete interval computation for depth 15, residue 19874. -/
theorem bounds_15_19874 : exactInterval 15 19874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19874 : oddCount 19874 15 = 8 ∧ acceleratedOrbit 15 19874 = 3982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19874) = 3 ^ 8 * m + 3982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19874.1, data_15_19874.2]

/-- Complete interval computation for depth 15, residue 19875. -/
theorem bounds_15_19875 : exactInterval 15 19875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19875 : oddCount 19875 15 = 8 ∧ acceleratedOrbit 15 19875 = 3982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19875) = 3 ^ 8 * m + 3982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19875.1, data_15_19875.2]

/-- Complete interval computation for depth 15, residue 19876. -/
theorem bounds_15_19876 : exactInterval 15 19876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19876 : oddCount 19876 15 = 8 ∧ acceleratedOrbit 15 19876 = 3982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19876) = 3 ^ 8 * m + 3982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19876.1, data_15_19876.2]

/-- Complete interval computation for depth 15, residue 19877. -/
theorem bounds_15_19877 : exactInterval 15 19877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19877 : oddCount 19877 15 = 8 ∧ acceleratedOrbit 15 19877 = 3982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19877) = 3 ^ 8 * m + 3982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19877.1, data_15_19877.2]

/-- Complete interval computation for depth 15, residue 19878. -/
theorem bounds_15_19878 : exactInterval 15 19878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19878 : oddCount 19878 15 = 8 ∧ acceleratedOrbit 15 19878 = 3982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19878) = 3 ^ 8 * m + 3982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19878.1, data_15_19878.2]

/-- Complete interval computation for depth 15, residue 19879. -/
theorem bounds_15_19879 : exactInterval 15 19879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19879 : oddCount 19879 15 = 10 ∧ acceleratedOrbit 15 19879 = 35828 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19879) = 3 ^ 10 * m + 35828 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19879.1, data_15_19879.2]

/-- Complete interval computation for depth 15, residue 19880. -/
theorem bounds_15_19880 : exactInterval 15 19880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19880 : oddCount 19880 15 = 6 ∧ acceleratedOrbit 15 19880 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19880) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19880.1, data_15_19880.2]

/-- Complete interval computation for depth 15, residue 19881. -/
theorem bounds_15_19881 : exactInterval 15 19881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19881 : oddCount 19881 15 = 7 ∧ acceleratedOrbit 15 19881 = 1327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19881) = 3 ^ 7 * m + 1327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19881.1, data_15_19881.2]

/-- Complete interval computation for depth 15, residue 19882. -/
theorem bounds_15_19882 : exactInterval 15 19882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19882 : oddCount 19882 15 = 6 ∧ acceleratedOrbit 15 19882 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19882) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19882.1, data_15_19882.2]

/-- Complete interval computation for depth 15, residue 19883. -/
theorem bounds_15_19883 : exactInterval 15 19883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19883 : oddCount 19883 15 = 9 ∧ acceleratedOrbit 15 19883 = 11945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19883) = 3 ^ 9 * m + 11945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19883.1, data_15_19883.2]

/-- Complete interval computation for depth 15, residue 19884. -/
theorem bounds_15_19884 : exactInterval 15 19884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19884 : oddCount 19884 15 = 6 ∧ acceleratedOrbit 15 19884 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19884) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19884.1, data_15_19884.2]

/-- Complete interval computation for depth 15, residue 19885. -/
theorem bounds_15_19885 : exactInterval 15 19885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19885 : oddCount 19885 15 = 6 ∧ acceleratedOrbit 15 19885 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19885) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19885.1, data_15_19885.2]

/-- Complete interval computation for depth 15, residue 19886. -/
theorem bounds_15_19886 : exactInterval 15 19886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19886 : oddCount 19886 15 = 6 ∧ acceleratedOrbit 15 19886 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19886) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19886.1, data_15_19886.2]

/-- Complete interval computation for depth 15, residue 19887. -/
theorem bounds_15_19887 : exactInterval 15 19887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19887 : oddCount 19887 15 = 10 ∧ acceleratedOrbit 15 19887 = 35842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19887) = 3 ^ 10 * m + 35842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19887.1, data_15_19887.2]

/-- Complete interval computation for depth 15, residue 19888. -/
theorem bounds_15_19888 : exactInterval 15 19888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19888 : oddCount 19888 15 = 6 ∧ acceleratedOrbit 15 19888 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19888) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19888.1, data_15_19888.2]

/-- Complete interval computation for depth 15, residue 19889. -/
theorem bounds_15_19889 : exactInterval 15 19889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19889 : oddCount 19889 15 = 6 ∧ acceleratedOrbit 15 19889 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19889) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19889.1, data_15_19889.2]

end Collatz.Research.PassageAtlas.Batch0607
