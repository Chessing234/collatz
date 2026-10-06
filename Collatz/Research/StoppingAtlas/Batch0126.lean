import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0126

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 896. -/
theorem bounds_11_896 : exactInterval 11 896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_896 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 896) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_896 : oddCount 896 11 = 3 ∧ acceleratedOrbit 11 896 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_896 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 896) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_896.1, data_11_896.2]

/-- Complete interval computation for depth 11, residue 897. -/
theorem bounds_11_897 : exactInterval 11 897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_897 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 897) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_897 : oddCount 897 11 = 7 ∧ acceleratedOrbit 11 897 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_897 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 897) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_897.1, data_11_897.2]

/-- Complete interval computation for depth 11, residue 898. -/
theorem bounds_11_898 : exactInterval 11 898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_898 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 898) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_898 : oddCount 898 11 = 6 ∧ acceleratedOrbit 11 898 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_898 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 898) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_898.1, data_11_898.2]

/-- Complete interval computation for depth 11, residue 899. -/
theorem bounds_11_899 : exactInterval 11 899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_899 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 899) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_899 : oddCount 899 11 = 6 ∧ acceleratedOrbit 11 899 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_899 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 899) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_899.1, data_11_899.2]

/-- Complete interval computation for depth 11, residue 900. -/
theorem bounds_11_900 : exactInterval 11 900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_900 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 900) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_900 : oddCount 900 11 = 7 ∧ acceleratedOrbit 11 900 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_900 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 900) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_900.1, data_11_900.2]

/-- Complete interval computation for depth 11, residue 901. -/
theorem bounds_11_901 : exactInterval 11 901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_901 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 901) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_901 : oddCount 901 11 = 7 ∧ acceleratedOrbit 11 901 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_901 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 901) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_901.1, data_11_901.2]

/-- Complete interval computation for depth 11, residue 902. -/
theorem bounds_11_902 : exactInterval 11 902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_902 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 902) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_902 : oddCount 902 11 = 7 ∧ acceleratedOrbit 11 902 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_902 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 902) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_902.1, data_11_902.2]

/-- Complete interval computation for depth 11, residue 903. -/
theorem bounds_11_903 : exactInterval 11 903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_903 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 903) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_903 : oddCount 903 11 = 6 ∧ acceleratedOrbit 11 903 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_903 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 903) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_903.1, data_11_903.2]

/-- Complete interval computation for depth 11, residue 904. -/
theorem bounds_11_904 : exactInterval 11 904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_904 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 904) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_904 : oddCount 904 11 = 2 ∧ acceleratedOrbit 11 904 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_904 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 904) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_904.1, data_11_904.2]

/-- Complete interval computation for depth 11, residue 905. -/
theorem bounds_11_905 : exactInterval 11 905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_905 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 905) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_905 : oddCount 905 11 = 8 ∧ acceleratedOrbit 11 905 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_905 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 905) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_905.1, data_11_905.2]

/-- Complete interval computation for depth 11, residue 906. -/
theorem bounds_11_906 : exactInterval 11 906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_906 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 906) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_906 : oddCount 906 11 = 2 ∧ acceleratedOrbit 11 906 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_906 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 906) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_906.1, data_11_906.2]

/-- Complete interval computation for depth 11, residue 907. -/
theorem bounds_11_907 : exactInterval 11 907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_907 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 907) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_907 : oddCount 907 11 = 8 ∧ acceleratedOrbit 11 907 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_907 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 907) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_907.1, data_11_907.2]

/-- Complete interval computation for depth 11, residue 908. -/
theorem bounds_11_908 : exactInterval 11 908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_908 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 908) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_908 : oddCount 908 11 = 2 ∧ acceleratedOrbit 11 908 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_908 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 908) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_908.1, data_11_908.2]

/-- Complete interval computation for depth 11, residue 909. -/
theorem bounds_11_909 : exactInterval 11 909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_909 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 909) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_909 : oddCount 909 11 = 2 ∧ acceleratedOrbit 11 909 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_909 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 909) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_909.1, data_11_909.2]

/-- Complete interval computation for depth 11, residue 910. -/
theorem bounds_11_910 : exactInterval 11 910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_910 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 910) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_910 : oddCount 910 11 = 6 ∧ acceleratedOrbit 11 910 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_910 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 910) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_910.1, data_11_910.2]

end Collatz.Research.StoppingAtlas.Batch0126
