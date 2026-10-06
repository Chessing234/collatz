import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0424

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13860. -/
theorem bounds_15_13860 : exactInterval 15 13860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13860 : oddCount 13860 15 = 7 ∧ acceleratedOrbit 15 13860 = 926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13860) = 3 ^ 7 * m + 926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13860.1, data_15_13860.2]

/-- Complete interval computation for depth 15, residue 13861. -/
theorem bounds_15_13861 : exactInterval 15 13861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13861 : oddCount 13861 15 = 7 ∧ acceleratedOrbit 15 13861 = 926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13861) = 3 ^ 7 * m + 926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13861.1, data_15_13861.2]

/-- Complete interval computation for depth 15, residue 13862. -/
theorem bounds_15_13862 : exactInterval 15 13862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13862 : oddCount 13862 15 = 7 ∧ acceleratedOrbit 15 13862 = 926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13862) = 3 ^ 7 * m + 926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13862.1, data_15_13862.2]

/-- Complete interval computation for depth 15, residue 13863. -/
theorem bounds_15_13863 : exactInterval 15 13863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13863 : oddCount 13863 15 = 7 ∧ acceleratedOrbit 15 13863 = 926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13863) = 3 ^ 7 * m + 926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13863.1, data_15_13863.2]

/-- Complete interval computation for depth 15, residue 13864. -/
theorem bounds_15_13864 : exactInterval 15 13864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13864 : oddCount 13864 15 = 4 ∧ acceleratedOrbit 15 13864 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13864) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13864.1, data_15_13864.2]

/-- Complete interval computation for depth 15, residue 13865. -/
theorem bounds_15_13865 : exactInterval 15 13865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13865 : oddCount 13865 15 = 12 ∧ acceleratedOrbit 15 13865 = 224896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13865) = 3 ^ 12 * m + 224896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13865.1, data_15_13865.2]

/-- Complete interval computation for depth 15, residue 13866. -/
theorem bounds_15_13866 : exactInterval 15 13866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13866 : oddCount 13866 15 = 4 ∧ acceleratedOrbit 15 13866 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13866) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13866.1, data_15_13866.2]

/-- Complete interval computation for depth 15, residue 13867. -/
theorem bounds_15_13867 : exactInterval 15 13867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13867 : oddCount 13867 15 = 8 ∧ acceleratedOrbit 15 13867 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13867) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13867.1, data_15_13867.2]

/-- Complete interval computation for depth 15, residue 13868. -/
theorem bounds_15_13868 : exactInterval 15 13868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13868 : oddCount 13868 15 = 8 ∧ acceleratedOrbit 15 13868 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13868) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13868.1, data_15_13868.2]

/-- Complete interval computation for depth 15, residue 13869. -/
theorem bounds_15_13869 : exactInterval 15 13869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13869 : oddCount 13869 15 = 8 ∧ acceleratedOrbit 15 13869 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13869) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13869.1, data_15_13869.2]

/-- Complete interval computation for depth 15, residue 13870. -/
theorem bounds_15_13870 : exactInterval 15 13870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13870 : oddCount 13870 15 = 8 ∧ acceleratedOrbit 15 13870 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13870) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13870.1, data_15_13870.2]

/-- Complete interval computation for depth 15, residue 13871. -/
theorem bounds_15_13871 : exactInterval 15 13871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13871 : oddCount 13871 15 = 11 ∧ acceleratedOrbit 15 13871 = 74996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13871) = 3 ^ 11 * m + 74996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13871.1, data_15_13871.2]

/-- Complete interval computation for depth 15, residue 13872. -/
theorem bounds_15_13872 : exactInterval 15 13872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13872 : oddCount 13872 15 = 4 ∧ acceleratedOrbit 15 13872 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13872) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13872.1, data_15_13872.2]

/-- Complete interval computation for depth 15, residue 13873. -/
theorem bounds_15_13873 : exactInterval 15 13873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13873 : oddCount 13873 15 = 9 ∧ acceleratedOrbit 15 13873 = 8338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13873) = 3 ^ 9 * m + 8338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13873.1, data_15_13873.2]

/-- Complete interval computation for depth 15, residue 13874. -/
theorem bounds_15_13874 : exactInterval 15 13874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13874 : oddCount 13874 15 = 9 ∧ acceleratedOrbit 15 13874 = 8338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13874) = 3 ^ 9 * m + 8338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13874.1, data_15_13874.2]

/-- Complete interval computation for depth 15, residue 13875. -/
theorem bounds_15_13875 : exactInterval 15 13875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13875 : oddCount 13875 15 = 9 ∧ acceleratedOrbit 15 13875 = 8338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13875) = 3 ^ 9 * m + 8338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13875.1, data_15_13875.2]

/-- Complete interval computation for depth 15, residue 13876. -/
theorem bounds_15_13876 : exactInterval 15 13876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13876 : oddCount 13876 15 = 4 ∧ acceleratedOrbit 15 13876 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13876) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13876.1, data_15_13876.2]

/-- Complete interval computation for depth 15, residue 13877. -/
theorem bounds_15_13877 : exactInterval 15 13877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13877 : oddCount 13877 15 = 4 ∧ acceleratedOrbit 15 13877 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13877) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13877.1, data_15_13877.2]

/-- Complete interval computation for depth 15, residue 13878. -/
theorem bounds_15_13878 : exactInterval 15 13878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13878 : oddCount 13878 15 = 12 ∧ acceleratedOrbit 15 13878 = 225125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13878) = 3 ^ 12 * m + 225125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13878.1, data_15_13878.2]

/-- Complete interval computation for depth 15, residue 13879. -/
theorem bounds_15_13879 : exactInterval 15 13879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13879 : oddCount 13879 15 = 12 ∧ acceleratedOrbit 15 13879 = 225125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13879) = 3 ^ 12 * m + 225125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13879.1, data_15_13879.2]

/-- Complete interval computation for depth 15, residue 13880. -/
theorem bounds_15_13880 : exactInterval 15 13880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13880 : oddCount 13880 15 = 5 ∧ acceleratedOrbit 15 13880 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13880) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13880.1, data_15_13880.2]

/-- Complete interval computation for depth 15, residue 13881. -/
theorem bounds_15_13881 : exactInterval 15 13881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13881 : oddCount 13881 15 = 9 ∧ acceleratedOrbit 15 13881 = 8342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13881) = 3 ^ 9 * m + 8342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13881.1, data_15_13881.2]

/-- Complete interval computation for depth 15, residue 13882. -/
theorem bounds_15_13882 : exactInterval 15 13882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13882 : oddCount 13882 15 = 5 ∧ acceleratedOrbit 15 13882 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13882) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13882.1, data_15_13882.2]

/-- Complete interval computation for depth 15, residue 13883. -/
theorem bounds_15_13883 : exactInterval 15 13883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13883 : oddCount 13883 15 = 10 ∧ acceleratedOrbit 15 13883 = 25028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13883) = 3 ^ 10 * m + 25028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13883.1, data_15_13883.2]

/-- Complete interval computation for depth 15, residue 13884. -/
theorem bounds_15_13884 : exactInterval 15 13884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13884 : oddCount 13884 15 = 5 ∧ acceleratedOrbit 15 13884 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13884) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13884.1, data_15_13884.2]

/-- Complete interval computation for depth 15, residue 13885. -/
theorem bounds_15_13885 : exactInterval 15 13885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13885 : oddCount 13885 15 = 5 ∧ acceleratedOrbit 15 13885 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13885) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13885.1, data_15_13885.2]

/-- Complete interval computation for depth 15, residue 13886. -/
theorem bounds_15_13886 : exactInterval 15 13886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13886 : oddCount 13886 15 = 11 ∧ acceleratedOrbit 15 13886 = 75086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13886) = 3 ^ 11 * m + 75086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13886.1, data_15_13886.2]

/-- Complete interval computation for depth 15, residue 13887. -/
theorem bounds_15_13887 : exactInterval 15 13887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13887 : oddCount 13887 15 = 11 ∧ acceleratedOrbit 15 13887 = 75086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13887) = 3 ^ 11 * m + 75086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13887.1, data_15_13887.2]

/-- Complete interval computation for depth 15, residue 13888. -/
theorem bounds_15_13888 : exactInterval 15 13888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13888 : oddCount 13888 15 = 4 ∧ acceleratedOrbit 15 13888 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13888) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13888.1, data_15_13888.2]

/-- Complete interval computation for depth 15, residue 13889. -/
theorem bounds_15_13889 : exactInterval 15 13889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13889 : oddCount 13889 15 = 7 ∧ acceleratedOrbit 15 13889 = 928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13889) = 3 ^ 7 * m + 928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13889.1, data_15_13889.2]

/-- Complete interval computation for depth 15, residue 13890. -/
theorem bounds_15_13890 : exactInterval 15 13890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13890 : oddCount 13890 15 = 7 ∧ acceleratedOrbit 15 13890 = 928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13890) = 3 ^ 7 * m + 928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13890.1, data_15_13890.2]

/-- Complete interval computation for depth 15, residue 13891. -/
theorem bounds_15_13891 : exactInterval 15 13891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13891 : oddCount 13891 15 = 7 ∧ acceleratedOrbit 15 13891 = 928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13891) = 3 ^ 7 * m + 928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13891.1, data_15_13891.2]

/-- Complete interval computation for depth 15, residue 13892. -/
theorem bounds_15_13892 : exactInterval 15 13892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13892 : oddCount 13892 15 = 6 ∧ acceleratedOrbit 15 13892 = 310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13892) = 3 ^ 6 * m + 310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13892.1, data_15_13892.2]

end Collatz.Research.PassageAtlas.Batch0424
