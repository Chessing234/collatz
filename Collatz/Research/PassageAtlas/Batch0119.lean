import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0119

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3866. -/
theorem bounds_15_3866 : exactInterval 15 3866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3866 : oddCount 3866 15 = 4 ∧ acceleratedOrbit 15 3866 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3866) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3866.1, data_15_3866.2]

/-- Complete interval computation for depth 15, residue 3867. -/
theorem bounds_15_3867 : exactInterval 15 3867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3867 : oddCount 3867 15 = 10 ∧ acceleratedOrbit 15 3867 = 6971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3867) = 3 ^ 10 * m + 6971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3867.1, data_15_3867.2]

/-- Complete interval computation for depth 15, residue 3868. -/
theorem bounds_15_3868 : exactInterval 15 3868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3868 : oddCount 3868 15 = 8 ∧ acceleratedOrbit 15 3868 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3868) = 3 ^ 8 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3868.1, data_15_3868.2]

/-- Complete interval computation for depth 15, residue 3869. -/
theorem bounds_15_3869 : exactInterval 15 3869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3869 : oddCount 3869 15 = 8 ∧ acceleratedOrbit 15 3869 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3869) = 3 ^ 8 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3869.1, data_15_3869.2]

/-- Complete interval computation for depth 15, residue 3870. -/
theorem bounds_15_3870 : exactInterval 15 3870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3870 : oddCount 3870 15 = 8 ∧ acceleratedOrbit 15 3870 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3870) = 3 ^ 8 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3870.1, data_15_3870.2]

/-- Complete interval computation for depth 15, residue 3871. -/
theorem bounds_15_3871 : exactInterval 15 3871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3871 : oddCount 3871 15 = 10 ∧ acceleratedOrbit 15 3871 = 6979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3871) = 3 ^ 10 * m + 6979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3871.1, data_15_3871.2]

/-- Complete interval computation for depth 15, residue 3872. -/
theorem bounds_15_3872 : exactInterval 15 3872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3872 : oddCount 3872 15 = 7 ∧ acceleratedOrbit 15 3872 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3872) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3872.1, data_15_3872.2]

/-- Complete interval computation for depth 15, residue 3873. -/
theorem bounds_15_3873 : exactInterval 15 3873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3873 : oddCount 3873 15 = 7 ∧ acceleratedOrbit 15 3873 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3873) = 3 ^ 7 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3873.1, data_15_3873.2]

/-- Complete interval computation for depth 15, residue 3874. -/
theorem bounds_15_3874 : exactInterval 15 3874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3874 : oddCount 3874 15 = 7 ∧ acceleratedOrbit 15 3874 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3874) = 3 ^ 7 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3874.1, data_15_3874.2]

/-- Complete interval computation for depth 15, residue 3875. -/
theorem bounds_15_3875 : exactInterval 15 3875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3875 : oddCount 3875 15 = 7 ∧ acceleratedOrbit 15 3875 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3875) = 3 ^ 7 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3875.1, data_15_3875.2]

/-- Complete interval computation for depth 15, residue 3876. -/
theorem bounds_15_3876 : exactInterval 15 3876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3876 : oddCount 3876 15 = 7 ∧ acceleratedOrbit 15 3876 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3876) = 3 ^ 7 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3876.1, data_15_3876.2]

/-- Complete interval computation for depth 15, residue 3877. -/
theorem bounds_15_3877 : exactInterval 15 3877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3877 : oddCount 3877 15 = 7 ∧ acceleratedOrbit 15 3877 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3877) = 3 ^ 7 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3877.1, data_15_3877.2]

/-- Complete interval computation for depth 15, residue 3878. -/
theorem bounds_15_3878 : exactInterval 15 3878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3878 : oddCount 3878 15 = 7 ∧ acceleratedOrbit 15 3878 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3878) = 3 ^ 7 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3878.1, data_15_3878.2]

/-- Complete interval computation for depth 15, residue 3879. -/
theorem bounds_15_3879 : exactInterval 15 3879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3879 : oddCount 3879 15 = 7 ∧ acceleratedOrbit 15 3879 = 259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3879) = 3 ^ 7 * m + 259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3879.1, data_15_3879.2]

/-- Complete interval computation for depth 15, residue 3880. -/
theorem bounds_15_3880 : exactInterval 15 3880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3880 : oddCount 3880 15 = 7 ∧ acceleratedOrbit 15 3880 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3880) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3880.1, data_15_3880.2]

/-- Complete interval computation for depth 15, residue 3881. -/
theorem bounds_15_3881 : exactInterval 15 3881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3881 : oddCount 3881 15 = 8 ∧ acceleratedOrbit 15 3881 = 778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3881) = 3 ^ 8 * m + 778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3881.1, data_15_3881.2]

/-- Complete interval computation for depth 15, residue 3882. -/
theorem bounds_15_3882 : exactInterval 15 3882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3882 : oddCount 3882 15 = 7 ∧ acceleratedOrbit 15 3882 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3882) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3882.1, data_15_3882.2]

/-- Complete interval computation for depth 15, residue 3883. -/
theorem bounds_15_3883 : exactInterval 15 3883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3883 : oddCount 3883 15 = 7 ∧ acceleratedOrbit 15 3883 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3883) = 3 ^ 7 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3883.1, data_15_3883.2]

/-- Complete interval computation for depth 15, residue 3884. -/
theorem bounds_15_3884 : exactInterval 15 3884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3884 : oddCount 3884 15 = 5 ∧ acceleratedOrbit 15 3884 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3884) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3884.1, data_15_3884.2]

/-- Complete interval computation for depth 15, residue 3885. -/
theorem bounds_15_3885 : exactInterval 15 3885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3885 : oddCount 3885 15 = 5 ∧ acceleratedOrbit 15 3885 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3885) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3885.1, data_15_3885.2]

/-- Complete interval computation for depth 15, residue 3886. -/
theorem bounds_15_3886 : exactInterval 15 3886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3886 : oddCount 3886 15 = 5 ∧ acceleratedOrbit 15 3886 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3886) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3886.1, data_15_3886.2]

/-- Complete interval computation for depth 15, residue 3887. -/
theorem bounds_15_3887 : exactInterval 15 3887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3887 : oddCount 3887 15 = 7 ∧ acceleratedOrbit 15 3887 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3887) = 3 ^ 7 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3887.1, data_15_3887.2]

/-- Complete interval computation for depth 15, residue 3888. -/
theorem bounds_15_3888 : exactInterval 15 3888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3888 : oddCount 3888 15 = 7 ∧ acceleratedOrbit 15 3888 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3888) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3888.1, data_15_3888.2]

/-- Complete interval computation for depth 15, residue 3889. -/
theorem bounds_15_3889 : exactInterval 15 3889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3889 : oddCount 3889 15 = 5 ∧ acceleratedOrbit 15 3889 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3889) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3889.1, data_15_3889.2]

/-- Complete interval computation for depth 15, residue 3890. -/
theorem bounds_15_3890 : exactInterval 15 3890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3890 : oddCount 3890 15 = 5 ∧ acceleratedOrbit 15 3890 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3890) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3890.1, data_15_3890.2]

/-- Complete interval computation for depth 15, residue 3891. -/
theorem bounds_15_3891 : exactInterval 15 3891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3891 : oddCount 3891 15 = 5 ∧ acceleratedOrbit 15 3891 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3891) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3891.1, data_15_3891.2]

/-- Complete interval computation for depth 15, residue 3892. -/
theorem bounds_15_3892 : exactInterval 15 3892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3892 : oddCount 3892 15 = 7 ∧ acceleratedOrbit 15 3892 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3892) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3892.1, data_15_3892.2]

/-- Complete interval computation for depth 15, residue 3893. -/
theorem bounds_15_3893 : exactInterval 15 3893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3893 : oddCount 3893 15 = 7 ∧ acceleratedOrbit 15 3893 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3893) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3893.1, data_15_3893.2]

/-- Complete interval computation for depth 15, residue 3894. -/
theorem bounds_15_3894 : exactInterval 15 3894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3894 : oddCount 3894 15 = 9 ∧ acceleratedOrbit 15 3894 = 2342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3894) = 3 ^ 9 * m + 2342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3894.1, data_15_3894.2]

/-- Complete interval computation for depth 15, residue 3895. -/
theorem bounds_15_3895 : exactInterval 15 3895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3895 : oddCount 3895 15 = 9 ∧ acceleratedOrbit 15 3895 = 2342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3895) = 3 ^ 9 * m + 2342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3895.1, data_15_3895.2]

/-- Complete interval computation for depth 15, residue 3896. -/
theorem bounds_15_3896 : exactInterval 15 3896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3896 : oddCount 3896 15 = 9 ∧ acceleratedOrbit 15 3896 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3896) = 3 ^ 9 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3896.1, data_15_3896.2]

/-- Complete interval computation for depth 15, residue 3897. -/
theorem bounds_15_3897 : exactInterval 15 3897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3897 : oddCount 3897 15 = 8 ∧ acceleratedOrbit 15 3897 = 782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3897) = 3 ^ 8 * m + 782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3897.1, data_15_3897.2]

/-- Complete interval computation for depth 15, residue 3898. -/
theorem bounds_15_3898 : exactInterval 15 3898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3898 : oddCount 3898 15 = 9 ∧ acceleratedOrbit 15 3898 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3898) = 3 ^ 9 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3898.1, data_15_3898.2]

end Collatz.Research.PassageAtlas.Batch0119
