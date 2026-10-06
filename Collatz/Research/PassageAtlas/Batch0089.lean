import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0089

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2883. -/
theorem bounds_15_2883 : exactInterval 15 2883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2883 : oddCount 2883 15 = 7 ∧ acceleratedOrbit 15 2883 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2883) = 3 ^ 7 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2883.1, data_15_2883.2]

/-- Complete interval computation for depth 15, residue 2884. -/
theorem bounds_15_2884 : exactInterval 15 2884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2884 : oddCount 2884 15 = 6 ∧ acceleratedOrbit 15 2884 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2884) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2884.1, data_15_2884.2]

/-- Complete interval computation for depth 15, residue 2885. -/
theorem bounds_15_2885 : exactInterval 15 2885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2885 : oddCount 2885 15 = 6 ∧ acceleratedOrbit 15 2885 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2885) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2885.1, data_15_2885.2]

/-- Complete interval computation for depth 15, residue 2886. -/
theorem bounds_15_2886 : exactInterval 15 2886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2886 : oddCount 2886 15 = 6 ∧ acceleratedOrbit 15 2886 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2886) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2886.1, data_15_2886.2]

/-- Complete interval computation for depth 15, residue 2887. -/
theorem bounds_15_2887 : exactInterval 15 2887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2887 : oddCount 2887 15 = 10 ∧ acceleratedOrbit 15 2887 = 5206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2887) = 3 ^ 10 * m + 5206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2887.1, data_15_2887.2]

/-- Complete interval computation for depth 15, residue 2888. -/
theorem bounds_15_2888 : exactInterval 15 2888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2888 : oddCount 2888 15 = 6 ∧ acceleratedOrbit 15 2888 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2888) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2888.1, data_15_2888.2]

/-- Complete interval computation for depth 15, residue 2889. -/
theorem bounds_15_2889 : exactInterval 15 2889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2889 : oddCount 2889 15 = 8 ∧ acceleratedOrbit 15 2889 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2889) = 3 ^ 8 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2889.1, data_15_2889.2]

/-- Complete interval computation for depth 15, residue 2890. -/
theorem bounds_15_2890 : exactInterval 15 2890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2890 : oddCount 2890 15 = 6 ∧ acceleratedOrbit 15 2890 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2890) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2890.1, data_15_2890.2]

/-- Complete interval computation for depth 15, residue 2891. -/
theorem bounds_15_2891 : exactInterval 15 2891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2891 : oddCount 2891 15 = 6 ∧ acceleratedOrbit 15 2891 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2891) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2891.1, data_15_2891.2]

/-- Complete interval computation for depth 15, residue 2892. -/
theorem bounds_15_2892 : exactInterval 15 2892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2892 : oddCount 2892 15 = 6 ∧ acceleratedOrbit 15 2892 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2892) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2892.1, data_15_2892.2]

/-- Complete interval computation for depth 15, residue 2893. -/
theorem bounds_15_2893 : exactInterval 15 2893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2893 : oddCount 2893 15 = 6 ∧ acceleratedOrbit 15 2893 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2893) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2893.1, data_15_2893.2]

/-- Complete interval computation for depth 15, residue 2894. -/
theorem bounds_15_2894 : exactInterval 15 2894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2894 : oddCount 2894 15 = 9 ∧ acceleratedOrbit 15 2894 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2894) = 3 ^ 9 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2894.1, data_15_2894.2]

/-- Complete interval computation for depth 15, residue 2895. -/
theorem bounds_15_2895 : exactInterval 15 2895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2895 : oddCount 2895 15 = 9 ∧ acceleratedOrbit 15 2895 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2895) = 3 ^ 9 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2895.1, data_15_2895.2]

/-- Complete interval computation for depth 15, residue 2896. -/
theorem bounds_15_2896 : exactInterval 15 2896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2896 : oddCount 2896 15 = 4 ∧ acceleratedOrbit 15 2896 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2896) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2896.1, data_15_2896.2]

/-- Complete interval computation for depth 15, residue 2897. -/
theorem bounds_15_2897 : exactInterval 15 2897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2897 : oddCount 2897 15 = 8 ∧ acceleratedOrbit 15 2897 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2897) = 3 ^ 8 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2897.1, data_15_2897.2]

/-- Complete interval computation for depth 15, residue 2898. -/
theorem bounds_15_2898 : exactInterval 15 2898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2898 : oddCount 2898 15 = 8 ∧ acceleratedOrbit 15 2898 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2898) = 3 ^ 8 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2898.1, data_15_2898.2]

/-- Complete interval computation for depth 15, residue 2899. -/
theorem bounds_15_2899 : exactInterval 15 2899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2899 : oddCount 2899 15 = 8 ∧ acceleratedOrbit 15 2899 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2899) = 3 ^ 8 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2899.1, data_15_2899.2]

/-- Complete interval computation for depth 15, residue 2900. -/
theorem bounds_15_2900 : exactInterval 15 2900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2900 : oddCount 2900 15 = 4 ∧ acceleratedOrbit 15 2900 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2900) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2900.1, data_15_2900.2]

/-- Complete interval computation for depth 15, residue 2901. -/
theorem bounds_15_2901 : exactInterval 15 2901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2901 : oddCount 2901 15 = 4 ∧ acceleratedOrbit 15 2901 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2901) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2901.1, data_15_2901.2]

/-- Complete interval computation for depth 15, residue 2902. -/
theorem bounds_15_2902 : exactInterval 15 2902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2902 : oddCount 2902 15 = 7 ∧ acceleratedOrbit 15 2902 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2902) = 3 ^ 7 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2902.1, data_15_2902.2]

/-- Complete interval computation for depth 15, residue 2903. -/
theorem bounds_15_2903 : exactInterval 15 2903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2903 : oddCount 2903 15 = 7 ∧ acceleratedOrbit 15 2903 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2903) = 3 ^ 7 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2903.1, data_15_2903.2]

/-- Complete interval computation for depth 15, residue 2904. -/
theorem bounds_15_2904 : exactInterval 15 2904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2904 : oddCount 2904 15 = 6 ∧ acceleratedOrbit 15 2904 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2904) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2904.1, data_15_2904.2]

/-- Complete interval computation for depth 15, residue 2905. -/
theorem bounds_15_2905 : exactInterval 15 2905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2905 : oddCount 2905 15 = 6 ∧ acceleratedOrbit 15 2905 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2905) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2905.1, data_15_2905.2]

/-- Complete interval computation for depth 15, residue 2906. -/
theorem bounds_15_2906 : exactInterval 15 2906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2906 : oddCount 2906 15 = 6 ∧ acceleratedOrbit 15 2906 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2906) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2906.1, data_15_2906.2]

/-- Complete interval computation for depth 15, residue 2907. -/
theorem bounds_15_2907 : exactInterval 15 2907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2907 : oddCount 2907 15 = 9 ∧ acceleratedOrbit 15 2907 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2907) = 3 ^ 9 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2907.1, data_15_2907.2]

/-- Complete interval computation for depth 15, residue 2908. -/
theorem bounds_15_2908 : exactInterval 15 2908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2908 : oddCount 2908 15 = 6 ∧ acceleratedOrbit 15 2908 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2908) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2908.1, data_15_2908.2]

/-- Complete interval computation for depth 15, residue 2909. -/
theorem bounds_15_2909 : exactInterval 15 2909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2909 : oddCount 2909 15 = 6 ∧ acceleratedOrbit 15 2909 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2909) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2909.1, data_15_2909.2]

/-- Complete interval computation for depth 15, residue 2910. -/
theorem bounds_15_2910 : exactInterval 15 2910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2910 : oddCount 2910 15 = 8 ∧ acceleratedOrbit 15 2910 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2910) = 3 ^ 8 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2910.1, data_15_2910.2]

/-- Complete interval computation for depth 15, residue 2911. -/
theorem bounds_15_2911 : exactInterval 15 2911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2911 : oddCount 2911 15 = 8 ∧ acceleratedOrbit 15 2911 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2911) = 3 ^ 8 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2911.1, data_15_2911.2]

/-- Complete interval computation for depth 15, residue 2912. -/
theorem bounds_15_2912 : exactInterval 15 2912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2912 : oddCount 2912 15 = 8 ∧ acceleratedOrbit 15 2912 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2912) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2912.1, data_15_2912.2]

/-- Complete interval computation for depth 15, residue 2913. -/
theorem bounds_15_2913 : exactInterval 15 2913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2913 : oddCount 2913 15 = 10 ∧ acceleratedOrbit 15 2913 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2913) = 3 ^ 10 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2913.1, data_15_2913.2]

/-- Complete interval computation for depth 15, residue 2914. -/
theorem bounds_15_2914 : exactInterval 15 2914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2914 : oddCount 2914 15 = 5 ∧ acceleratedOrbit 15 2914 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2914) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2914.1, data_15_2914.2]

/-- Complete interval computation for depth 15, residue 2915. -/
theorem bounds_15_2915 : exactInterval 15 2915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2915 : oddCount 2915 15 = 5 ∧ acceleratedOrbit 15 2915 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2915) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2915.1, data_15_2915.2]

end Collatz.Research.PassageAtlas.Batch0089
