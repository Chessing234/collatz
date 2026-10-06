import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0655

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2877. -/
theorem bounds_13_2877 : exactInterval 13 2877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2877 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2877) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2877 : oddCount 2877 13 = 8 ∧ acceleratedOrbit 13 2877 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2877 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2877) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2877.1, data_13_2877.2]

/-- Complete interval computation for depth 13, residue 2878. -/
theorem bounds_13_2878 : exactInterval 13 2878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2878 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2878) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2878 : oddCount 2878 13 = 10 ∧ acceleratedOrbit 13 2878 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2878 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2878) = 3 ^ 10 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2878.1, data_13_2878.2]

/-- Complete interval computation for depth 13, residue 2879. -/
theorem bounds_13_2879 : exactInterval 13 2879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2879 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2879) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2879 : oddCount 2879 13 = 10 ∧ acceleratedOrbit 13 2879 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2879 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2879) = 3 ^ 10 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2879.1, data_13_2879.2]

/-- Complete interval computation for depth 13, residue 2880. -/
theorem bounds_13_2880 : exactInterval 13 2880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2880 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2880) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2880 : oddCount 2880 13 = 3 ∧ acceleratedOrbit 13 2880 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2880 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2880) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2880.1, data_13_2880.2]

/-- Complete interval computation for depth 13, residue 2881. -/
theorem bounds_13_2881 : exactInterval 13 2881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2881 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2881) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2881 : oddCount 2881 13 = 4 ∧ acceleratedOrbit 13 2881 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2881 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2881) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2881.1, data_13_2881.2]

/-- Complete interval computation for depth 13, residue 2882. -/
theorem bounds_13_2882 : exactInterval 13 2882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2882 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2882) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2882 : oddCount 2882 13 = 6 ∧ acceleratedOrbit 13 2882 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2882 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2882) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2882.1, data_13_2882.2]

/-- Complete interval computation for depth 13, residue 2883. -/
theorem bounds_13_2883 : exactInterval 13 2883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2883 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2883) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2883 : oddCount 2883 13 = 6 ∧ acceleratedOrbit 13 2883 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2883 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2883) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2883.1, data_13_2883.2]

/-- Complete interval computation for depth 13, residue 2884. -/
theorem bounds_13_2884 : exactInterval 13 2884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2884 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2884) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2884 : oddCount 2884 13 = 5 ∧ acceleratedOrbit 13 2884 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2884 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2884) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2884.1, data_13_2884.2]

/-- Complete interval computation for depth 13, residue 2885. -/
theorem bounds_13_2885 : exactInterval 13 2885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2885 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2885) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2885 : oddCount 2885 13 = 5 ∧ acceleratedOrbit 13 2885 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2885 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2885) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2885.1, data_13_2885.2]

/-- Complete interval computation for depth 13, residue 2886. -/
theorem bounds_13_2886 : exactInterval 13 2886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2886 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2886) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2886 : oddCount 2886 13 = 5 ∧ acceleratedOrbit 13 2886 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2886 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2886) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2886.1, data_13_2886.2]

/-- Complete interval computation for depth 13, residue 2887. -/
theorem bounds_13_2887 : exactInterval 13 2887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2887 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2887) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2887 : oddCount 2887 13 = 9 ∧ acceleratedOrbit 13 2887 = 6941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2887 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2887) = 3 ^ 9 * m + 6941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2887.1, data_13_2887.2]

/-- Complete interval computation for depth 13, residue 2888. -/
theorem bounds_13_2888 : exactInterval 13 2888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2888 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2888) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2888 : oddCount 2888 13 = 5 ∧ acceleratedOrbit 13 2888 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2888 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2888) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2888.1, data_13_2888.2]

/-- Complete interval computation for depth 13, residue 2889. -/
theorem bounds_13_2889 : exactInterval 13 2889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2889 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2889) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2889 : oddCount 2889 13 = 7 ∧ acceleratedOrbit 13 2889 = 773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2889 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2889) = 3 ^ 7 * m + 773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2889.1, data_13_2889.2]

/-- Complete interval computation for depth 13, residue 2890. -/
theorem bounds_13_2890 : exactInterval 13 2890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2890 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2890) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2890 : oddCount 2890 13 = 5 ∧ acceleratedOrbit 13 2890 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2890 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2890) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2890.1, data_13_2890.2]

/-- Complete interval computation for depth 13, residue 2891. -/
theorem bounds_13_2891 : exactInterval 13 2891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2891 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2891) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2891 : oddCount 2891 13 = 5 ∧ acceleratedOrbit 13 2891 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2891 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2891) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2891.1, data_13_2891.2]

end Collatz.Research.StoppingAtlas.Batch0655
