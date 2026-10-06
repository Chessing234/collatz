import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0729

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23855. -/
theorem bounds_15_23855 : exactInterval 15 23855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23855 : oddCount 23855 15 = 11 ∧ acceleratedOrbit 15 23855 = 128972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23855) = 3 ^ 11 * m + 128972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23855.1, data_15_23855.2]

/-- Complete interval computation for depth 15, residue 23856. -/
theorem bounds_15_23856 : exactInterval 15 23856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23856 : oddCount 23856 15 = 7 ∧ acceleratedOrbit 15 23856 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23856) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23856.1, data_15_23856.2]

/-- Complete interval computation for depth 15, residue 23857. -/
theorem bounds_15_23857 : exactInterval 15 23857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23857 : oddCount 23857 15 = 10 ∧ acceleratedOrbit 15 23857 = 43010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23857) = 3 ^ 10 * m + 43010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23857.1, data_15_23857.2]

/-- Complete interval computation for depth 15, residue 23858. -/
theorem bounds_15_23858 : exactInterval 15 23858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23858 : oddCount 23858 15 = 10 ∧ acceleratedOrbit 15 23858 = 43010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23858) = 3 ^ 10 * m + 43010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23858.1, data_15_23858.2]

/-- Complete interval computation for depth 15, residue 23859. -/
theorem bounds_15_23859 : exactInterval 15 23859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23859 : oddCount 23859 15 = 10 ∧ acceleratedOrbit 15 23859 = 43010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23859) = 3 ^ 10 * m + 43010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23859.1, data_15_23859.2]

/-- Complete interval computation for depth 15, residue 23860. -/
theorem bounds_15_23860 : exactInterval 15 23860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23860 : oddCount 23860 15 = 7 ∧ acceleratedOrbit 15 23860 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23860) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23860.1, data_15_23860.2]

/-- Complete interval computation for depth 15, residue 23861. -/
theorem bounds_15_23861 : exactInterval 15 23861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23861 : oddCount 23861 15 = 7 ∧ acceleratedOrbit 15 23861 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23861) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23861.1, data_15_23861.2]

/-- Complete interval computation for depth 15, residue 23862. -/
theorem bounds_15_23862 : exactInterval 15 23862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23862 : oddCount 23862 15 = 10 ∧ acceleratedOrbit 15 23862 = 43006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23862) = 3 ^ 10 * m + 43006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23862.1, data_15_23862.2]

/-- Complete interval computation for depth 15, residue 23863. -/
theorem bounds_15_23863 : exactInterval 15 23863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23863 : oddCount 23863 15 = 10 ∧ acceleratedOrbit 15 23863 = 43006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23863) = 3 ^ 10 * m + 43006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23863.1, data_15_23863.2]

/-- Complete interval computation for depth 15, residue 23864. -/
theorem bounds_15_23864 : exactInterval 15 23864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23864 : oddCount 23864 15 = 8 ∧ acceleratedOrbit 15 23864 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23864) = 3 ^ 8 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23864.1, data_15_23864.2]

/-- Complete interval computation for depth 15, residue 23865. -/
theorem bounds_15_23865 : exactInterval 15 23865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23865 : oddCount 23865 15 = 12 ∧ acceleratedOrbit 15 23865 = 387098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23865) = 3 ^ 12 * m + 387098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23865.1, data_15_23865.2]

/-- Complete interval computation for depth 15, residue 23866. -/
theorem bounds_15_23866 : exactInterval 15 23866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23866 : oddCount 23866 15 = 8 ∧ acceleratedOrbit 15 23866 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23866) = 3 ^ 8 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23866.1, data_15_23866.2]

/-- Complete interval computation for depth 15, residue 23867. -/
theorem bounds_15_23867 : exactInterval 15 23867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23867 : oddCount 23867 15 = 4 ∧ acceleratedOrbit 15 23867 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23867) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23867.1, data_15_23867.2]

/-- Complete interval computation for depth 15, residue 23868. -/
theorem bounds_15_23868 : exactInterval 15 23868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23868 : oddCount 23868 15 = 8 ∧ acceleratedOrbit 15 23868 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23868) = 3 ^ 8 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23868.1, data_15_23868.2]

/-- Complete interval computation for depth 15, residue 23869. -/
theorem bounds_15_23869 : exactInterval 15 23869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23869 : oddCount 23869 15 = 8 ∧ acceleratedOrbit 15 23869 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23869) = 3 ^ 8 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23869.1, data_15_23869.2]

/-- Complete interval computation for depth 15, residue 23870. -/
theorem bounds_15_23870 : exactInterval 15 23870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23870 : oddCount 23870 15 = 10 ∧ acceleratedOrbit 15 23870 = 43019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23870) = 3 ^ 10 * m + 43019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23870.1, data_15_23870.2]

/-- Complete interval computation for depth 15, residue 23871. -/
theorem bounds_15_23871 : exactInterval 15 23871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23871 : oddCount 23871 15 = 10 ∧ acceleratedOrbit 15 23871 = 43019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23871) = 3 ^ 10 * m + 43019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23871.1, data_15_23871.2]

/-- Complete interval computation for depth 15, residue 23872. -/
theorem bounds_15_23872 : exactInterval 15 23872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23872 : oddCount 23872 15 = 3 ∧ acceleratedOrbit 15 23872 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23872) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23872.1, data_15_23872.2]

/-- Complete interval computation for depth 15, residue 23873. -/
theorem bounds_15_23873 : exactInterval 15 23873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23873 : oddCount 23873 15 = 7 ∧ acceleratedOrbit 15 23873 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23873) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23873.1, data_15_23873.2]

/-- Complete interval computation for depth 15, residue 23874. -/
theorem bounds_15_23874 : exactInterval 15 23874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23874 : oddCount 23874 15 = 7 ∧ acceleratedOrbit 15 23874 = 1594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23874) = 3 ^ 7 * m + 1594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23874.1, data_15_23874.2]

/-- Complete interval computation for depth 15, residue 23875. -/
theorem bounds_15_23875 : exactInterval 15 23875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23875 : oddCount 23875 15 = 7 ∧ acceleratedOrbit 15 23875 = 1594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23875) = 3 ^ 7 * m + 1594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23875.1, data_15_23875.2]

/-- Complete interval computation for depth 15, residue 23876. -/
theorem bounds_15_23876 : exactInterval 15 23876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23876 : oddCount 23876 15 = 7 ∧ acceleratedOrbit 15 23876 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23876) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23876.1, data_15_23876.2]

/-- Complete interval computation for depth 15, residue 23877. -/
theorem bounds_15_23877 : exactInterval 15 23877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23877 : oddCount 23877 15 = 7 ∧ acceleratedOrbit 15 23877 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23877) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23877.1, data_15_23877.2]

/-- Complete interval computation for depth 15, residue 23878. -/
theorem bounds_15_23878 : exactInterval 15 23878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23878 : oddCount 23878 15 = 7 ∧ acceleratedOrbit 15 23878 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23878) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23878.1, data_15_23878.2]

/-- Complete interval computation for depth 15, residue 23879. -/
theorem bounds_15_23879 : exactInterval 15 23879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23879 : oddCount 23879 15 = 9 ∧ acceleratedOrbit 15 23879 = 14345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23879) = 3 ^ 9 * m + 14345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23879.1, data_15_23879.2]

/-- Complete interval computation for depth 15, residue 23880. -/
theorem bounds_15_23880 : exactInterval 15 23880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23880 : oddCount 23880 15 = 8 ∧ acceleratedOrbit 15 23880 = 4784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23880) = 3 ^ 8 * m + 4784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23880.1, data_15_23880.2]

/-- Complete interval computation for depth 15, residue 23881. -/
theorem bounds_15_23881 : exactInterval 15 23881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23881 : oddCount 23881 15 = 9 ∧ acceleratedOrbit 15 23881 = 14347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23881) = 3 ^ 9 * m + 14347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23881.1, data_15_23881.2]

/-- Complete interval computation for depth 15, residue 23882. -/
theorem bounds_15_23882 : exactInterval 15 23882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23882 : oddCount 23882 15 = 8 ∧ acceleratedOrbit 15 23882 = 4784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23882) = 3 ^ 8 * m + 4784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23882.1, data_15_23882.2]

/-- Complete interval computation for depth 15, residue 23883. -/
theorem bounds_15_23883 : exactInterval 15 23883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23883 : oddCount 23883 15 = 7 ∧ acceleratedOrbit 15 23883 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23883) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23883.1, data_15_23883.2]

/-- Complete interval computation for depth 15, residue 23884. -/
theorem bounds_15_23884 : exactInterval 15 23884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23884 : oddCount 23884 15 = 8 ∧ acceleratedOrbit 15 23884 = 4784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23884) = 3 ^ 8 * m + 4784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23884.1, data_15_23884.2]

/-- Complete interval computation for depth 15, residue 23885. -/
theorem bounds_15_23885 : exactInterval 15 23885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23885 : oddCount 23885 15 = 8 ∧ acceleratedOrbit 15 23885 = 4784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23885) = 3 ^ 8 * m + 4784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23885.1, data_15_23885.2]

/-- Complete interval computation for depth 15, residue 23886. -/
theorem bounds_15_23886 : exactInterval 15 23886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23886 : oddCount 23886 15 = 9 ∧ acceleratedOrbit 15 23886 = 14350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23886) = 3 ^ 9 * m + 14350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23886.1, data_15_23886.2]

end Collatz.Research.PassageAtlas.Batch0729
