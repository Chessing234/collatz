import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0656

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2892. -/
theorem bounds_13_2892 : exactInterval 13 2892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2892 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2892) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2892 : oddCount 2892 13 = 5 ∧ acceleratedOrbit 13 2892 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2892 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2892) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2892.1, data_13_2892.2]

/-- Complete interval computation for depth 13, residue 2893. -/
theorem bounds_13_2893 : exactInterval 13 2893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2893 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2893) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2893 : oddCount 2893 13 = 5 ∧ acceleratedOrbit 13 2893 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2893 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2893) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2893.1, data_13_2893.2]

/-- Complete interval computation for depth 13, residue 2894. -/
theorem bounds_13_2894 : exactInterval 13 2894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2894 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2894) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2894 : oddCount 2894 13 = 8 ∧ acceleratedOrbit 13 2894 = 2321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2894 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2894) = 3 ^ 8 * m + 2321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2894.1, data_13_2894.2]

/-- Complete interval computation for depth 13, residue 2895. -/
theorem bounds_13_2895 : exactInterval 13 2895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2895 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2895) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2895 : oddCount 2895 13 = 8 ∧ acceleratedOrbit 13 2895 = 2321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2895 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2895) = 3 ^ 8 * m + 2321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2895.1, data_13_2895.2]

/-- Complete interval computation for depth 13, residue 2896. -/
theorem bounds_13_2896 : exactInterval 13 2896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2896 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2896) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2896 : oddCount 2896 13 = 3 ∧ acceleratedOrbit 13 2896 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2896 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2896) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2896.1, data_13_2896.2]

/-- Complete interval computation for depth 13, residue 2897. -/
theorem bounds_13_2897 : exactInterval 13 2897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2897 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2897) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2897 : oddCount 2897 13 = 8 ∧ acceleratedOrbit 13 2897 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2897 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2897) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2897.1, data_13_2897.2]

/-- Complete interval computation for depth 13, residue 2898. -/
theorem bounds_13_2898 : exactInterval 13 2898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2898 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2898) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2898 : oddCount 2898 13 = 8 ∧ acceleratedOrbit 13 2898 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2898 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2898) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2898.1, data_13_2898.2]

/-- Complete interval computation for depth 13, residue 2899. -/
theorem bounds_13_2899 : exactInterval 13 2899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2899 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2899) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2899 : oddCount 2899 13 = 8 ∧ acceleratedOrbit 13 2899 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2899 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2899) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2899.1, data_13_2899.2]

/-- Complete interval computation for depth 13, residue 2900. -/
theorem bounds_13_2900 : exactInterval 13 2900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2900 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2900) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2900 : oddCount 2900 13 = 3 ∧ acceleratedOrbit 13 2900 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2900 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2900) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2900.1, data_13_2900.2]

/-- Complete interval computation for depth 13, residue 2901. -/
theorem bounds_13_2901 : exactInterval 13 2901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2901 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2901) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2901 : oddCount 2901 13 = 3 ∧ acceleratedOrbit 13 2901 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2901 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2901) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2901.1, data_13_2901.2]

/-- Complete interval computation for depth 13, residue 2902. -/
theorem bounds_13_2902 : exactInterval 13 2902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2902 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2902) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2902 : oddCount 2902 13 = 7 ∧ acceleratedOrbit 13 2902 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2902 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2902) = 3 ^ 7 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2902.1, data_13_2902.2]

/-- Complete interval computation for depth 13, residue 2903. -/
theorem bounds_13_2903 : exactInterval 13 2903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2903 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2903) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2903 : oddCount 2903 13 = 7 ∧ acceleratedOrbit 13 2903 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2903 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2903) = 3 ^ 7 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2903.1, data_13_2903.2]

/-- Complete interval computation for depth 13, residue 2904. -/
theorem bounds_13_2904 : exactInterval 13 2904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2904 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2904) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2904 : oddCount 2904 13 = 6 ∧ acceleratedOrbit 13 2904 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2904 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2904) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2904.1, data_13_2904.2]

/-- Complete interval computation for depth 13, residue 2905. -/
theorem bounds_13_2905 : exactInterval 13 2905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2905 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2905) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2905 : oddCount 2905 13 = 6 ∧ acceleratedOrbit 13 2905 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2905 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2905) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2905.1, data_13_2905.2]

/-- Complete interval computation for depth 13, residue 2906. -/
theorem bounds_13_2906 : exactInterval 13 2906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2906 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2906) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2906 : oddCount 2906 13 = 6 ∧ acceleratedOrbit 13 2906 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2906 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2906) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2906.1, data_13_2906.2]

/-- Complete interval computation for depth 13, residue 2907. -/
theorem bounds_13_2907 : exactInterval 13 2907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2907 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2907) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2907 : oddCount 2907 13 = 8 ∧ acceleratedOrbit 13 2907 = 2330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2907 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2907) = 3 ^ 8 * m + 2330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2907.1, data_13_2907.2]

end Collatz.Research.StoppingAtlas.Batch0656
