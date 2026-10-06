import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0720

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3875. -/
theorem bounds_13_3875 : exactInterval 13 3875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3875 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3875) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3875 : oddCount 3875 13 = 6 ∧ acceleratedOrbit 13 3875 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3875 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3875) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3875.1, data_13_3875.2]

/-- Complete interval computation for depth 13, residue 3876. -/
theorem bounds_13_3876 : exactInterval 13 3876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3876 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3876) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3876 : oddCount 3876 13 = 6 ∧ acceleratedOrbit 13 3876 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3876 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3876) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3876.1, data_13_3876.2]

/-- Complete interval computation for depth 13, residue 3877. -/
theorem bounds_13_3877 : exactInterval 13 3877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3877 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3877) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3877 : oddCount 3877 13 = 6 ∧ acceleratedOrbit 13 3877 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3877 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3877) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3877.1, data_13_3877.2]

/-- Complete interval computation for depth 13, residue 3878. -/
theorem bounds_13_3878 : exactInterval 13 3878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3878 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3878) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3878 : oddCount 3878 13 = 6 ∧ acceleratedOrbit 13 3878 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3878 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3878) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3878.1, data_13_3878.2]

/-- Complete interval computation for depth 13, residue 3879. -/
theorem bounds_13_3879 : exactInterval 13 3879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3879 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3879) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3879 : oddCount 3879 13 = 7 ∧ acceleratedOrbit 13 3879 = 1036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3879 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3879) = 3 ^ 7 * m + 1036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3879.1, data_13_3879.2]

/-- Complete interval computation for depth 13, residue 3880. -/
theorem bounds_13_3880 : exactInterval 13 3880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3880 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3880) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3880 : oddCount 3880 13 = 6 ∧ acceleratedOrbit 13 3880 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3880 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3880) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3880.1, data_13_3880.2]

/-- Complete interval computation for depth 13, residue 3881. -/
theorem bounds_13_3881 : exactInterval 13 3881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3881 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3881) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3881 : oddCount 3881 13 = 7 ∧ acceleratedOrbit 13 3881 = 1037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3881 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3881) = 3 ^ 7 * m + 1037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3881.1, data_13_3881.2]

/-- Complete interval computation for depth 13, residue 3882. -/
theorem bounds_13_3882 : exactInterval 13 3882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3882 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3882) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3882 : oddCount 3882 13 = 6 ∧ acceleratedOrbit 13 3882 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3882 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3882) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3882.1, data_13_3882.2]

/-- Complete interval computation for depth 13, residue 3883. -/
theorem bounds_13_3883 : exactInterval 13 3883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3883 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3883) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3883 : oddCount 3883 13 = 6 ∧ acceleratedOrbit 13 3883 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3883 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3883) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3883.1, data_13_3883.2]

/-- Complete interval computation for depth 13, residue 3884. -/
theorem bounds_13_3884 : exactInterval 13 3884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3884 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3884) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3884 : oddCount 3884 13 = 5 ∧ acceleratedOrbit 13 3884 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3884 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3884) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3884.1, data_13_3884.2]

/-- Complete interval computation for depth 13, residue 3885. -/
theorem bounds_13_3885 : exactInterval 13 3885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3885 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3885) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3885 : oddCount 3885 13 = 5 ∧ acceleratedOrbit 13 3885 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3885 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3885) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3885.1, data_13_3885.2]

/-- Complete interval computation for depth 13, residue 3886. -/
theorem bounds_13_3886 : exactInterval 13 3886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3886 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3886) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3886 : oddCount 3886 13 = 5 ∧ acceleratedOrbit 13 3886 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3886 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3886) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3886.1, data_13_3886.2]

/-- Complete interval computation for depth 13, residue 3887. -/
theorem bounds_13_3887 : exactInterval 13 3887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3887 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3887) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3887 : oddCount 3887 13 = 6 ∧ acceleratedOrbit 13 3887 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3887 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3887) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3887.1, data_13_3887.2]

/-- Complete interval computation for depth 13, residue 3888. -/
theorem bounds_13_3888 : exactInterval 13 3888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3888 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3888) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3888 : oddCount 3888 13 = 6 ∧ acceleratedOrbit 13 3888 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3888 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3888) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3888.1, data_13_3888.2]

/-- Complete interval computation for depth 13, residue 3889. -/
theorem bounds_13_3889 : exactInterval 13 3889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3889 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3889) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3889 : oddCount 3889 13 = 5 ∧ acceleratedOrbit 13 3889 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3889 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3889) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3889.1, data_13_3889.2]

/-- Complete interval computation for depth 13, residue 3890. -/
theorem bounds_13_3890 : exactInterval 13 3890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3890 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3890) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3890 : oddCount 3890 13 = 5 ∧ acceleratedOrbit 13 3890 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3890 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3890) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3890.1, data_13_3890.2]

end Collatz.Research.StoppingAtlas.Batch0720
