import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0389

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2887. -/
theorem bounds_12_2887 : exactInterval 12 2887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2887 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2887) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2887 : oddCount 2887 12 = 8 ∧ acceleratedOrbit 12 2887 = 4627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2887 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2887) = 3 ^ 8 * m + 4627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2887.1, data_12_2887.2]

/-- Complete interval computation for depth 12, residue 2888. -/
theorem bounds_12_2888 : exactInterval 12 2888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2888 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2888) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2888 : oddCount 2888 12 = 5 ∧ acceleratedOrbit 12 2888 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2888 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2888) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2888.1, data_12_2888.2]

/-- Complete interval computation for depth 12, residue 2889. -/
theorem bounds_12_2889 : exactInterval 12 2889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2889 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2889) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2889 : oddCount 2889 12 = 6 ∧ acceleratedOrbit 12 2889 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2889 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2889) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2889.1, data_12_2889.2]

/-- Complete interval computation for depth 12, residue 2890. -/
theorem bounds_12_2890 : exactInterval 12 2890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2890 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2890) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2890 : oddCount 2890 12 = 5 ∧ acceleratedOrbit 12 2890 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2890 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2890) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2890.1, data_12_2890.2]

/-- Complete interval computation for depth 12, residue 2891. -/
theorem bounds_12_2891 : exactInterval 12 2891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2891 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2891) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2891 : oddCount 2891 12 = 5 ∧ acceleratedOrbit 12 2891 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2891 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2891) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2891.1, data_12_2891.2]

/-- Complete interval computation for depth 12, residue 2892. -/
theorem bounds_12_2892 : exactInterval 12 2892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2892 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2892) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2892 : oddCount 2892 12 = 5 ∧ acceleratedOrbit 12 2892 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2892 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2892) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2892.1, data_12_2892.2]

/-- Complete interval computation for depth 12, residue 2893. -/
theorem bounds_12_2893 : exactInterval 12 2893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2893 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2893) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2893 : oddCount 2893 12 = 5 ∧ acceleratedOrbit 12 2893 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2893 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2893) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2893.1, data_12_2893.2]

/-- Complete interval computation for depth 12, residue 2894. -/
theorem bounds_12_2894 : exactInterval 12 2894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2894 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2894) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2894 : oddCount 2894 12 = 7 ∧ acceleratedOrbit 12 2894 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2894 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2894) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2894.1, data_12_2894.2]

/-- Complete interval computation for depth 12, residue 2895. -/
theorem bounds_12_2895 : exactInterval 12 2895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2895 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2895) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2895 : oddCount 2895 12 = 7 ∧ acceleratedOrbit 12 2895 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2895 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2895) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2895.1, data_12_2895.2]

/-- Complete interval computation for depth 12, residue 2896. -/
theorem bounds_12_2896 : exactInterval 12 2896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2896 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2896) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2896 : oddCount 2896 12 = 3 ∧ acceleratedOrbit 12 2896 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2896 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2896) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2896.1, data_12_2896.2]

/-- Complete interval computation for depth 12, residue 2897. -/
theorem bounds_12_2897 : exactInterval 12 2897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2897 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2897) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2897 : oddCount 2897 12 = 7 ∧ acceleratedOrbit 12 2897 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2897 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2897) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2897.1, data_12_2897.2]

/-- Complete interval computation for depth 12, residue 2898. -/
theorem bounds_12_2898 : exactInterval 12 2898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2898 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2898) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2898 : oddCount 2898 12 = 7 ∧ acceleratedOrbit 12 2898 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2898 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2898) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2898.1, data_12_2898.2]

/-- Complete interval computation for depth 12, residue 2899. -/
theorem bounds_12_2899 : exactInterval 12 2899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2899 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2899) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2899 : oddCount 2899 12 = 7 ∧ acceleratedOrbit 12 2899 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2899 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2899) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2899.1, data_12_2899.2]

/-- Complete interval computation for depth 12, residue 2900. -/
theorem bounds_12_2900 : exactInterval 12 2900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2900 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2900) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2900 : oddCount 2900 12 = 3 ∧ acceleratedOrbit 12 2900 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2900 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2900) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2900.1, data_12_2900.2]

/-- Complete interval computation for depth 12, residue 2901. -/
theorem bounds_12_2901 : exactInterval 12 2901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2901 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2901) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2901 : oddCount 2901 12 = 3 ∧ acceleratedOrbit 12 2901 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2901 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2901) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2901.1, data_12_2901.2]

/-- Complete interval computation for depth 12, residue 2902. -/
theorem bounds_12_2902 : exactInterval 12 2902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2902 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2902) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2902 : oddCount 2902 12 = 7 ∧ acceleratedOrbit 12 2902 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2902 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2902) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2902.1, data_12_2902.2]

end Collatz.Research.StoppingAtlas.Batch0389
