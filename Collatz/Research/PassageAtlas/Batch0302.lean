import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0302

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9863. -/
theorem bounds_15_9863 : exactInterval 15 9863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9863 : oddCount 9863 15 = 7 ∧ acceleratedOrbit 15 9863 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9863) = 3 ^ 7 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9863.1, data_15_9863.2]

/-- Complete interval computation for depth 15, residue 9864. -/
theorem bounds_15_9864 : exactInterval 15 9864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9864 : oddCount 9864 15 = 7 ∧ acceleratedOrbit 15 9864 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9864) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9864.1, data_15_9864.2]

/-- Complete interval computation for depth 15, residue 9865. -/
theorem bounds_15_9865 : exactInterval 15 9865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9865 : oddCount 9865 15 = 9 ∧ acceleratedOrbit 15 9865 = 5927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9865) = 3 ^ 9 * m + 5927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9865.1, data_15_9865.2]

/-- Complete interval computation for depth 15, residue 9866. -/
theorem bounds_15_9866 : exactInterval 15 9866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9866 : oddCount 9866 15 = 7 ∧ acceleratedOrbit 15 9866 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9866) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9866.1, data_15_9866.2]

/-- Complete interval computation for depth 15, residue 9867. -/
theorem bounds_15_9867 : exactInterval 15 9867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9867 : oddCount 9867 15 = 7 ∧ acceleratedOrbit 15 9867 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9867) = 3 ^ 7 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9867.1, data_15_9867.2]

/-- Complete interval computation for depth 15, residue 9868. -/
theorem bounds_15_9868 : exactInterval 15 9868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9868 : oddCount 9868 15 = 7 ∧ acceleratedOrbit 15 9868 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9868) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9868.1, data_15_9868.2]

/-- Complete interval computation for depth 15, residue 9869. -/
theorem bounds_15_9869 : exactInterval 15 9869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9869 : oddCount 9869 15 = 7 ∧ acceleratedOrbit 15 9869 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9869) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9869.1, data_15_9869.2]

/-- Complete interval computation for depth 15, residue 9870. -/
theorem bounds_15_9870 : exactInterval 15 9870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9870 : oddCount 9870 15 = 11 ∧ acceleratedOrbit 15 9870 = 53378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9870) = 3 ^ 11 * m + 53378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9870.1, data_15_9870.2]

/-- Complete interval computation for depth 15, residue 9871. -/
theorem bounds_15_9871 : exactInterval 15 9871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9871 : oddCount 9871 15 = 11 ∧ acceleratedOrbit 15 9871 = 53378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9871) = 3 ^ 11 * m + 53378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9871.1, data_15_9871.2]

/-- Complete interval computation for depth 15, residue 9872. -/
theorem bounds_15_9872 : exactInterval 15 9872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9872 : oddCount 9872 15 = 7 ∧ acceleratedOrbit 15 9872 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9872) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9872.1, data_15_9872.2]

/-- Complete interval computation for depth 15, residue 9873. -/
theorem bounds_15_9873 : exactInterval 15 9873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9873 : oddCount 9873 15 = 6 ∧ acceleratedOrbit 15 9873 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9873) = 3 ^ 6 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9873.1, data_15_9873.2]

/-- Complete interval computation for depth 15, residue 9874. -/
theorem bounds_15_9874 : exactInterval 15 9874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9874 : oddCount 9874 15 = 6 ∧ acceleratedOrbit 15 9874 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9874) = 3 ^ 6 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9874.1, data_15_9874.2]

/-- Complete interval computation for depth 15, residue 9875. -/
theorem bounds_15_9875 : exactInterval 15 9875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9875 : oddCount 9875 15 = 6 ∧ acceleratedOrbit 15 9875 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9875) = 3 ^ 6 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9875.1, data_15_9875.2]

/-- Complete interval computation for depth 15, residue 9876. -/
theorem bounds_15_9876 : exactInterval 15 9876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9876 : oddCount 9876 15 = 7 ∧ acceleratedOrbit 15 9876 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9876) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9876.1, data_15_9876.2]

/-- Complete interval computation for depth 15, residue 9877. -/
theorem bounds_15_9877 : exactInterval 15 9877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9877 : oddCount 9877 15 = 7 ∧ acceleratedOrbit 15 9877 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9877) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9877.1, data_15_9877.2]

/-- Complete interval computation for depth 15, residue 9878. -/
theorem bounds_15_9878 : exactInterval 15 9878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9878 : oddCount 9878 15 = 7 ∧ acceleratedOrbit 15 9878 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9878) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9878.1, data_15_9878.2]

/-- Complete interval computation for depth 15, residue 9879. -/
theorem bounds_15_9879 : exactInterval 15 9879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9879 : oddCount 9879 15 = 7 ∧ acceleratedOrbit 15 9879 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9879) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9879.1, data_15_9879.2]

/-- Complete interval computation for depth 15, residue 9880. -/
theorem bounds_15_9880 : exactInterval 15 9880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9880 : oddCount 9880 15 = 7 ∧ acceleratedOrbit 15 9880 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9880) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9880.1, data_15_9880.2]

/-- Complete interval computation for depth 15, residue 9881. -/
theorem bounds_15_9881 : exactInterval 15 9881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9881 : oddCount 9881 15 = 9 ∧ acceleratedOrbit 15 9881 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9881) = 3 ^ 9 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9881.1, data_15_9881.2]

/-- Complete interval computation for depth 15, residue 9882. -/
theorem bounds_15_9882 : exactInterval 15 9882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9882 : oddCount 9882 15 = 7 ∧ acceleratedOrbit 15 9882 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9882) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9882.1, data_15_9882.2]

/-- Complete interval computation for depth 15, residue 9883. -/
theorem bounds_15_9883 : exactInterval 15 9883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9883 : oddCount 9883 15 = 10 ∧ acceleratedOrbit 15 9883 = 17813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9883) = 3 ^ 10 * m + 17813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9883.1, data_15_9883.2]

/-- Complete interval computation for depth 15, residue 9884. -/
theorem bounds_15_9884 : exactInterval 15 9884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9884 : oddCount 9884 15 = 6 ∧ acceleratedOrbit 15 9884 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9884) = 3 ^ 6 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9884.1, data_15_9884.2]

/-- Complete interval computation for depth 15, residue 9885. -/
theorem bounds_15_9885 : exactInterval 15 9885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9885 : oddCount 9885 15 = 6 ∧ acceleratedOrbit 15 9885 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9885) = 3 ^ 6 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9885.1, data_15_9885.2]

/-- Complete interval computation for depth 15, residue 9886. -/
theorem bounds_15_9886 : exactInterval 15 9886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9886 : oddCount 9886 15 = 6 ∧ acceleratedOrbit 15 9886 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9886) = 3 ^ 6 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9886.1, data_15_9886.2]

/-- Complete interval computation for depth 15, residue 9887. -/
theorem bounds_15_9887 : exactInterval 15 9887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9887 : oddCount 9887 15 = 12 ∧ acceleratedOrbit 15 9887 = 160370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9887) = 3 ^ 12 * m + 160370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9887.1, data_15_9887.2]

/-- Complete interval computation for depth 15, residue 9888. -/
theorem bounds_15_9888 : exactInterval 15 9888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9888 : oddCount 9888 15 = 4 ∧ acceleratedOrbit 15 9888 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9888) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9888.1, data_15_9888.2]

/-- Complete interval computation for depth 15, residue 9889. -/
theorem bounds_15_9889 : exactInterval 15 9889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9889 : oddCount 9889 15 = 8 ∧ acceleratedOrbit 15 9889 = 1981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9889) = 3 ^ 8 * m + 1981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9889.1, data_15_9889.2]

/-- Complete interval computation for depth 15, residue 9890. -/
theorem bounds_15_9890 : exactInterval 15 9890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9890 : oddCount 9890 15 = 8 ∧ acceleratedOrbit 15 9890 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9890) = 3 ^ 8 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9890.1, data_15_9890.2]

/-- Complete interval computation for depth 15, residue 9891. -/
theorem bounds_15_9891 : exactInterval 15 9891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9891 : oddCount 9891 15 = 8 ∧ acceleratedOrbit 15 9891 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9891) = 3 ^ 8 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9891.1, data_15_9891.2]

/-- Complete interval computation for depth 15, residue 9892. -/
theorem bounds_15_9892 : exactInterval 15 9892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9892 : oddCount 9892 15 = 8 ∧ acceleratedOrbit 15 9892 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9892) = 3 ^ 8 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9892.1, data_15_9892.2]

/-- Complete interval computation for depth 15, residue 9893. -/
theorem bounds_15_9893 : exactInterval 15 9893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9893 : oddCount 9893 15 = 8 ∧ acceleratedOrbit 15 9893 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9893) = 3 ^ 8 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9893.1, data_15_9893.2]

/-- Complete interval computation for depth 15, residue 9894. -/
theorem bounds_15_9894 : exactInterval 15 9894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9894 : oddCount 9894 15 = 8 ∧ acceleratedOrbit 15 9894 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9894) = 3 ^ 8 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9894.1, data_15_9894.2]

end Collatz.Research.PassageAtlas.Batch0302
