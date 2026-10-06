import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0821

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26869. -/
theorem bounds_15_26869 : exactInterval 15 26869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26869 : oddCount 26869 15 = 7 ∧ acceleratedOrbit 15 26869 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26869) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26869.1, data_15_26869.2]

/-- Complete interval computation for depth 15, residue 26870. -/
theorem bounds_15_26870 : exactInterval 15 26870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26870 : oddCount 26870 15 = 9 ∧ acceleratedOrbit 15 26870 = 16145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26870) = 3 ^ 9 * m + 16145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26870.1, data_15_26870.2]

/-- Complete interval computation for depth 15, residue 26871. -/
theorem bounds_15_26871 : exactInterval 15 26871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26871 : oddCount 26871 15 = 9 ∧ acceleratedOrbit 15 26871 = 16145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26871) = 3 ^ 9 * m + 16145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26871.1, data_15_26871.2]

/-- Complete interval computation for depth 15, residue 26872. -/
theorem bounds_15_26872 : exactInterval 15 26872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26872 : oddCount 26872 15 = 6 ∧ acceleratedOrbit 15 26872 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26872) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26872.1, data_15_26872.2]

/-- Complete interval computation for depth 15, residue 26873. -/
theorem bounds_15_26873 : exactInterval 15 26873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26873 : oddCount 26873 15 = 9 ∧ acceleratedOrbit 15 26873 = 16145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26873) = 3 ^ 9 * m + 16145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26873.1, data_15_26873.2]

/-- Complete interval computation for depth 15, residue 26874. -/
theorem bounds_15_26874 : exactInterval 15 26874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26874 : oddCount 26874 15 = 6 ∧ acceleratedOrbit 15 26874 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26874) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26874.1, data_15_26874.2]

/-- Complete interval computation for depth 15, residue 26875. -/
theorem bounds_15_26875 : exactInterval 15 26875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26875 : oddCount 26875 15 = 10 ∧ acceleratedOrbit 15 26875 = 48433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26875) = 3 ^ 10 * m + 48433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26875.1, data_15_26875.2]

/-- Complete interval computation for depth 15, residue 26876. -/
theorem bounds_15_26876 : exactInterval 15 26876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26876 : oddCount 26876 15 = 6 ∧ acceleratedOrbit 15 26876 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26876) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26876.1, data_15_26876.2]

/-- Complete interval computation for depth 15, residue 26877. -/
theorem bounds_15_26877 : exactInterval 15 26877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26877 : oddCount 26877 15 = 6 ∧ acceleratedOrbit 15 26877 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26877) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26877.1, data_15_26877.2]

/-- Complete interval computation for depth 15, residue 26878. -/
theorem bounds_15_26878 : exactInterval 15 26878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26878 : oddCount 26878 15 = 10 ∧ acceleratedOrbit 15 26878 = 48439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26878) = 3 ^ 10 * m + 48439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26878.1, data_15_26878.2]

/-- Complete interval computation for depth 15, residue 26879. -/
theorem bounds_15_26879 : exactInterval 15 26879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26879 : oddCount 26879 15 = 10 ∧ acceleratedOrbit 15 26879 = 48439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26879) = 3 ^ 10 * m + 48439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26879.1, data_15_26879.2]

/-- Complete interval computation for depth 15, residue 26880. -/
theorem bounds_15_26880 : exactInterval 15 26880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26880 : oddCount 26880 15 = 5 ∧ acceleratedOrbit 15 26880 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26880) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26880.1, data_15_26880.2]

/-- Complete interval computation for depth 15, residue 26881. -/
theorem bounds_15_26881 : exactInterval 15 26881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26881 : oddCount 26881 15 = 7 ∧ acceleratedOrbit 15 26881 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26881) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26881.1, data_15_26881.2]

/-- Complete interval computation for depth 15, residue 26882. -/
theorem bounds_15_26882 : exactInterval 15 26882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26882 : oddCount 26882 15 = 8 ∧ acceleratedOrbit 15 26882 = 5384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26882) = 3 ^ 8 * m + 5384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26882.1, data_15_26882.2]

/-- Complete interval computation for depth 15, residue 26883. -/
theorem bounds_15_26883 : exactInterval 15 26883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26883 : oddCount 26883 15 = 8 ∧ acceleratedOrbit 15 26883 = 5384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26883) = 3 ^ 8 * m + 5384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26883.1, data_15_26883.2]

/-- Complete interval computation for depth 15, residue 26884. -/
theorem bounds_15_26884 : exactInterval 15 26884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26884 : oddCount 26884 15 = 5 ∧ acceleratedOrbit 15 26884 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26884) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26884.1, data_15_26884.2]

/-- Complete interval computation for depth 15, residue 26885. -/
theorem bounds_15_26885 : exactInterval 15 26885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26885 : oddCount 26885 15 = 5 ∧ acceleratedOrbit 15 26885 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26885) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26885.1, data_15_26885.2]

/-- Complete interval computation for depth 15, residue 26886. -/
theorem bounds_15_26886 : exactInterval 15 26886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26886 : oddCount 26886 15 = 5 ∧ acceleratedOrbit 15 26886 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26886) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26886.1, data_15_26886.2]

/-- Complete interval computation for depth 15, residue 26887. -/
theorem bounds_15_26887 : exactInterval 15 26887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26887 : oddCount 26887 15 = 8 ∧ acceleratedOrbit 15 26887 = 5384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26887) = 3 ^ 8 * m + 5384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26887.1, data_15_26887.2]

/-- Complete interval computation for depth 15, residue 26888. -/
theorem bounds_15_26888 : exactInterval 15 26888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26888 : oddCount 26888 15 = 5 ∧ acceleratedOrbit 15 26888 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26888) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26888.1, data_15_26888.2]

/-- Complete interval computation for depth 15, residue 26889. -/
theorem bounds_15_26889 : exactInterval 15 26889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26889 : oddCount 26889 15 = 7 ∧ acceleratedOrbit 15 26889 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26889) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26889.1, data_15_26889.2]

/-- Complete interval computation for depth 15, residue 26890. -/
theorem bounds_15_26890 : exactInterval 15 26890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26890 : oddCount 26890 15 = 5 ∧ acceleratedOrbit 15 26890 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26890) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26890.1, data_15_26890.2]

/-- Complete interval computation for depth 15, residue 26891. -/
theorem bounds_15_26891 : exactInterval 15 26891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26891 : oddCount 26891 15 = 8 ∧ acceleratedOrbit 15 26891 = 5386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26891) = 3 ^ 8 * m + 5386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26891.1, data_15_26891.2]

/-- Complete interval computation for depth 15, residue 26892. -/
theorem bounds_15_26892 : exactInterval 15 26892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26892 : oddCount 26892 15 = 5 ∧ acceleratedOrbit 15 26892 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26892) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26892.1, data_15_26892.2]

/-- Complete interval computation for depth 15, residue 26893. -/
theorem bounds_15_26893 : exactInterval 15 26893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26893 : oddCount 26893 15 = 5 ∧ acceleratedOrbit 15 26893 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26893) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26893.1, data_15_26893.2]

/-- Complete interval computation for depth 15, residue 26894. -/
theorem bounds_15_26894 : exactInterval 15 26894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26894 : oddCount 26894 15 = 9 ∧ acceleratedOrbit 15 26894 = 16159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26894) = 3 ^ 9 * m + 16159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26894.1, data_15_26894.2]

/-- Complete interval computation for depth 15, residue 26895. -/
theorem bounds_15_26895 : exactInterval 15 26895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26895 : oddCount 26895 15 = 9 ∧ acceleratedOrbit 15 26895 = 16159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26895) = 3 ^ 9 * m + 16159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26895.1, data_15_26895.2]

/-- Complete interval computation for depth 15, residue 26896. -/
theorem bounds_15_26896 : exactInterval 15 26896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26896 : oddCount 26896 15 = 5 ∧ acceleratedOrbit 15 26896 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26896) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26896.1, data_15_26896.2]

/-- Complete interval computation for depth 15, residue 26897. -/
theorem bounds_15_26897 : exactInterval 15 26897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26897 : oddCount 26897 15 = 5 ∧ acceleratedOrbit 15 26897 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26897) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26897.1, data_15_26897.2]

/-- Complete interval computation for depth 15, residue 26898. -/
theorem bounds_15_26898 : exactInterval 15 26898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26898 : oddCount 26898 15 = 11 ∧ acceleratedOrbit 15 26898 = 145435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26898) = 3 ^ 11 * m + 145435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26898.1, data_15_26898.2]

/-- Complete interval computation for depth 15, residue 26899. -/
theorem bounds_15_26899 : exactInterval 15 26899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26899 : oddCount 26899 15 = 11 ∧ acceleratedOrbit 15 26899 = 145435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26899) = 3 ^ 11 * m + 145435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26899.1, data_15_26899.2]

/-- Complete interval computation for depth 15, residue 26900. -/
theorem bounds_15_26900 : exactInterval 15 26900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26900 : oddCount 26900 15 = 5 ∧ acceleratedOrbit 15 26900 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26900) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26900.1, data_15_26900.2]

/-- Complete interval computation for depth 15, residue 26901. -/
theorem bounds_15_26901 : exactInterval 15 26901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26901 : oddCount 26901 15 = 5 ∧ acceleratedOrbit 15 26901 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26901) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26901.1, data_15_26901.2]

end Collatz.Research.PassageAtlas.Batch0821
