import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0980

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7869. -/
theorem bounds_13_7869 : exactInterval 13 7869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7869 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7869) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7869 : oddCount 7869 13 = 6 ∧ acceleratedOrbit 13 7869 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7869 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7869) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7869.1, data_13_7869.2]

/-- Complete interval computation for depth 13, residue 7870. -/
theorem bounds_13_7870 : exactInterval 13 7870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7870 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7870) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7870 : oddCount 7870 13 = 6 ∧ acceleratedOrbit 13 7870 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7870 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7870) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7870.1, data_13_7870.2]

/-- Complete interval computation for depth 13, residue 7871. -/
theorem bounds_13_7871 : exactInterval 13 7871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7871 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7871) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7871 : oddCount 7871 13 = 10 ∧ acceleratedOrbit 13 7871 = 56744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7871 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7871) = 3 ^ 10 * m + 56744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7871.1, data_13_7871.2]

/-- Complete interval computation for depth 13, residue 7872. -/
theorem bounds_13_7872 : exactInterval 13 7872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7872 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7872) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7872 : oddCount 7872 13 = 5 ∧ acceleratedOrbit 13 7872 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7872 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7872) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7872.1, data_13_7872.2]

/-- Complete interval computation for depth 13, residue 7873. -/
theorem bounds_13_7873 : exactInterval 13 7873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7873 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7873) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7873 : oddCount 7873 13 = 7 ∧ acceleratedOrbit 13 7873 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7873 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7873) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7873.1, data_13_7873.2]

/-- Complete interval computation for depth 13, residue 7874. -/
theorem bounds_13_7874 : exactInterval 13 7874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7874 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7874) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7874 : oddCount 7874 13 = 8 ∧ acceleratedOrbit 13 7874 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7874 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7874) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7874.1, data_13_7874.2]

/-- Complete interval computation for depth 13, residue 7875. -/
theorem bounds_13_7875 : exactInterval 13 7875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7875 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7875) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7875 : oddCount 7875 13 = 8 ∧ acceleratedOrbit 13 7875 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7875 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7875) = 3 ^ 8 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7875.1, data_13_7875.2]

/-- Complete interval computation for depth 13, residue 7876. -/
theorem bounds_13_7876 : exactInterval 13 7876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7876 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7876) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7876 : oddCount 7876 13 = 3 ∧ acceleratedOrbit 13 7876 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7876 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7876) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7876.1, data_13_7876.2]

/-- Complete interval computation for depth 13, residue 7877. -/
theorem bounds_13_7877 : exactInterval 13 7877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7877 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7877) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7877 : oddCount 7877 13 = 3 ∧ acceleratedOrbit 13 7877 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7877 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7877) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7877.1, data_13_7877.2]

/-- Complete interval computation for depth 13, residue 7878. -/
theorem bounds_13_7878 : exactInterval 13 7878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7878 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7878) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7878 : oddCount 7878 13 = 3 ∧ acceleratedOrbit 13 7878 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7878 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7878) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7878.1, data_13_7878.2]

/-- Complete interval computation for depth 13, residue 7879. -/
theorem bounds_13_7879 : exactInterval 13 7879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7879 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7879) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7879 : oddCount 7879 13 = 7 ∧ acceleratedOrbit 13 7879 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7879 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7879) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7879.1, data_13_7879.2]

/-- Complete interval computation for depth 13, residue 7880. -/
theorem bounds_13_7880 : exactInterval 13 7880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7880 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7880) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7880 : oddCount 7880 13 = 3 ∧ acceleratedOrbit 13 7880 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7880 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7880) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7880.1, data_13_7880.2]

/-- Complete interval computation for depth 13, residue 7881. -/
theorem bounds_13_7881 : exactInterval 13 7881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7881 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7881) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7881 : oddCount 7881 13 = 8 ∧ acceleratedOrbit 13 7881 = 6317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7881 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7881) = 3 ^ 8 * m + 6317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7881.1, data_13_7881.2]

/-- Complete interval computation for depth 13, residue 7882. -/
theorem bounds_13_7882 : exactInterval 13 7882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7882 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7882) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7882 : oddCount 7882 13 = 3 ∧ acceleratedOrbit 13 7882 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7882 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7882) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7882.1, data_13_7882.2]

/-- Complete interval computation for depth 13, residue 7883. -/
theorem bounds_13_7883 : exactInterval 13 7883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7883 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7883) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7883 : oddCount 7883 13 = 9 ∧ acceleratedOrbit 13 7883 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7883 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7883) = 3 ^ 9 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7883.1, data_13_7883.2]

end Collatz.Research.StoppingAtlas.Batch0980
