import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0526

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 896. -/
theorem bounds_13_896 : exactInterval 13 896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_896 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 896) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_896 : oddCount 896 13 = 4 ∧ acceleratedOrbit 13 896 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_896 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 896) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_896.1, data_13_896.2]

/-- Complete interval computation for depth 13, residue 897. -/
theorem bounds_13_897 : exactInterval 13 897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_897 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 897) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_897 : oddCount 897 13 = 8 ∧ acceleratedOrbit 13 897 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_897 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 897) = 3 ^ 8 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_897.1, data_13_897.2]

/-- Complete interval computation for depth 13, residue 898. -/
theorem bounds_13_898 : exactInterval 13 898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_898 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 898) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_898 : oddCount 898 13 = 8 ∧ acceleratedOrbit 13 898 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_898 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 898) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_898.1, data_13_898.2]

/-- Complete interval computation for depth 13, residue 899. -/
theorem bounds_13_899 : exactInterval 13 899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_899 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 899) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_899 : oddCount 899 13 = 8 ∧ acceleratedOrbit 13 899 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_899 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 899) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_899.1, data_13_899.2]

/-- Complete interval computation for depth 13, residue 900. -/
theorem bounds_13_900 : exactInterval 13 900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_900 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 900) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_900 : oddCount 900 13 = 9 ∧ acceleratedOrbit 13 900 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_900 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 900) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_900.1, data_13_900.2]

/-- Complete interval computation for depth 13, residue 901. -/
theorem bounds_13_901 : exactInterval 13 901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_901 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 901) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_901 : oddCount 901 13 = 9 ∧ acceleratedOrbit 13 901 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_901 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 901) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_901.1, data_13_901.2]

/-- Complete interval computation for depth 13, residue 902. -/
theorem bounds_13_902 : exactInterval 13 902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_902 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 902) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_902 : oddCount 902 13 = 9 ∧ acceleratedOrbit 13 902 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_902 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 902) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_902.1, data_13_902.2]

/-- Complete interval computation for depth 13, residue 903. -/
theorem bounds_13_903 : exactInterval 13 903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_903 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 903) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_903 : oddCount 903 13 = 8 ∧ acceleratedOrbit 13 903 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_903 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 903) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_903.1, data_13_903.2]

/-- Complete interval computation for depth 13, residue 904. -/
theorem bounds_13_904 : exactInterval 13 904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_904 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 904) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_904 : oddCount 904 13 = 2 ∧ acceleratedOrbit 13 904 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_904 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 904) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_904.1, data_13_904.2]

/-- Complete interval computation for depth 13, residue 905. -/
theorem bounds_13_905 : exactInterval 13 905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_905 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 905) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_905 : oddCount 905 13 = 9 ∧ acceleratedOrbit 13 905 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_905 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 905) = 3 ^ 9 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_905.1, data_13_905.2]

/-- Complete interval computation for depth 13, residue 906. -/
theorem bounds_13_906 : exactInterval 13 906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_906 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 906) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_906 : oddCount 906 13 = 2 ∧ acceleratedOrbit 13 906 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_906 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 906) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_906.1, data_13_906.2]

/-- Complete interval computation for depth 13, residue 907. -/
theorem bounds_13_907 : exactInterval 13 907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_907 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 907) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_907 : oddCount 907 13 = 10 ∧ acceleratedOrbit 13 907 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_907 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 907) = 3 ^ 10 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_907.1, data_13_907.2]

/-- Complete interval computation for depth 13, residue 908. -/
theorem bounds_13_908 : exactInterval 13 908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_908 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 908) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_908 : oddCount 908 13 = 2 ∧ acceleratedOrbit 13 908 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_908 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 908) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_908.1, data_13_908.2]

/-- Complete interval computation for depth 13, residue 909. -/
theorem bounds_13_909 : exactInterval 13 909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_909 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 909) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_909 : oddCount 909 13 = 2 ∧ acceleratedOrbit 13 909 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_909 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 909) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_909.1, data_13_909.2]

/-- Complete interval computation for depth 13, residue 910. -/
theorem bounds_13_910 : exactInterval 13 910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_910 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 910) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_910 : oddCount 910 13 = 7 ∧ acceleratedOrbit 13 910 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_910 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 910) = 3 ^ 7 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_910.1, data_13_910.2]

end Collatz.Research.StoppingAtlas.Batch0526
