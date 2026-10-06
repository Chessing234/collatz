import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0059

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 890. -/
theorem bounds_10_890 : exactInterval 10 890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_890 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 890) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_890 : oddCount 890 10 = 6 ∧ acceleratedOrbit 10 890 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_890 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 890) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_890.1, data_10_890.2]

/-- Complete interval computation for depth 10, residue 891. -/
theorem bounds_10_891 : exactInterval 10 891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_891 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 891) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_891 : oddCount 891 10 = 7 ∧ acceleratedOrbit 10 891 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_891 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 891) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_891.1, data_10_891.2]

/-- Complete interval computation for depth 10, residue 892. -/
theorem bounds_10_892 : exactInterval 10 892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_892 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 892) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_892 : oddCount 892 10 = 6 ∧ acceleratedOrbit 10 892 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_892 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 892) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_892.1, data_10_892.2]

/-- Complete interval computation for depth 10, residue 893. -/
theorem bounds_10_893 : exactInterval 10 893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_893 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 893) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_893 : oddCount 893 10 = 6 ∧ acceleratedOrbit 10 893 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_893 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 893) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_893.1, data_10_893.2]

/-- Complete interval computation for depth 10, residue 894. -/
theorem bounds_10_894 : exactInterval 10 894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_894 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 894) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_894 : oddCount 894 10 = 8 ∧ acceleratedOrbit 10 894 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_894 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 894) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_894.1, data_10_894.2]

/-- Complete interval computation for depth 10, residue 895. -/
theorem bounds_10_895 : exactInterval 10 895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_895 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 895) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_895 : oddCount 895 10 = 8 ∧ acceleratedOrbit 10 895 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_895 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 895) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_895.1, data_10_895.2]

/-- Complete interval computation for depth 10, residue 896. -/
theorem bounds_10_896 : exactInterval 10 896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_896 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 896) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_896 : oddCount 896 10 = 3 ∧ acceleratedOrbit 10 896 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_896 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 896) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_896.1, data_10_896.2]

/-- Complete interval computation for depth 10, residue 897. -/
theorem bounds_10_897 : exactInterval 10 897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_897 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 897) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_897 : oddCount 897 10 = 6 ∧ acceleratedOrbit 10 897 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_897 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 897) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_897.1, data_10_897.2]

/-- Complete interval computation for depth 10, residue 898. -/
theorem bounds_10_898 : exactInterval 10 898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_898 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 898) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_898 : oddCount 898 10 = 5 ∧ acceleratedOrbit 10 898 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_898 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 898) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_898.1, data_10_898.2]

/-- Complete interval computation for depth 10, residue 899. -/
theorem bounds_10_899 : exactInterval 10 899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_899 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 899) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_899 : oddCount 899 10 = 5 ∧ acceleratedOrbit 10 899 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_899 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 899) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_899.1, data_10_899.2]

/-- Complete interval computation for depth 10, residue 900. -/
theorem bounds_10_900 : exactInterval 10 900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_900 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 900) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_900 : oddCount 900 10 = 6 ∧ acceleratedOrbit 10 900 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_900 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 900) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_900.1, data_10_900.2]

/-- Complete interval computation for depth 10, residue 901. -/
theorem bounds_10_901 : exactInterval 10 901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_901 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 901) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_901 : oddCount 901 10 = 6 ∧ acceleratedOrbit 10 901 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_901 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 901) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_901.1, data_10_901.2]

/-- Complete interval computation for depth 10, residue 902. -/
theorem bounds_10_902 : exactInterval 10 902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_902 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 902) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_902 : oddCount 902 10 = 6 ∧ acceleratedOrbit 10 902 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_902 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 902) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_902.1, data_10_902.2]

/-- Complete interval computation for depth 10, residue 903. -/
theorem bounds_10_903 : exactInterval 10 903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_903 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 903) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_903 : oddCount 903 10 = 5 ∧ acceleratedOrbit 10 903 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_903 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 903) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_903.1, data_10_903.2]

/-- Complete interval computation for depth 10, residue 904. -/
theorem bounds_10_904 : exactInterval 10 904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_904 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 904) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_904 : oddCount 904 10 = 2 ∧ acceleratedOrbit 10 904 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_904 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 904) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_904.1, data_10_904.2]

/-- Complete interval computation for depth 10, residue 905. -/
theorem bounds_10_905 : exactInterval 10 905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_905 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 905) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_905 : oddCount 905 10 = 7 ∧ acceleratedOrbit 10 905 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_905 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 905) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_905.1, data_10_905.2]

end Collatz.Research.StoppingAtlas.Batch0059
