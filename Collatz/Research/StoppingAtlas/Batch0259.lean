import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0259

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 890. -/
theorem bounds_12_890 : exactInterval 12 890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_890 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 890) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_890 : oddCount 890 12 = 7 ∧ acceleratedOrbit 12 890 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_890 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 890) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_890.1, data_12_890.2]

/-- Complete interval computation for depth 12, residue 891. -/
theorem bounds_12_891 : exactInterval 12 891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_891 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 891) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_891 : oddCount 891 12 = 9 ∧ acceleratedOrbit 12 891 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_891 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 891) = 3 ^ 9 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_891.1, data_12_891.2]

/-- Complete interval computation for depth 12, residue 892. -/
theorem bounds_12_892 : exactInterval 12 892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_892 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 892) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_892 : oddCount 892 12 = 7 ∧ acceleratedOrbit 12 892 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_892 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 892) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_892.1, data_12_892.2]

/-- Complete interval computation for depth 12, residue 893. -/
theorem bounds_12_893 : exactInterval 12 893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_893 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 893) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_893 : oddCount 893 12 = 7 ∧ acceleratedOrbit 12 893 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_893 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 893) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_893.1, data_12_893.2]

/-- Complete interval computation for depth 12, residue 894. -/
theorem bounds_12_894 : exactInterval 12 894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_894 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 894) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_894 : oddCount 894 12 = 9 ∧ acceleratedOrbit 12 894 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_894 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 894) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_894.1, data_12_894.2]

/-- Complete interval computation for depth 12, residue 895. -/
theorem bounds_12_895 : exactInterval 12 895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_895 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 895) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_895 : oddCount 895 12 = 9 ∧ acceleratedOrbit 12 895 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_895 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 895) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_895.1, data_12_895.2]

/-- Complete interval computation for depth 12, residue 896. -/
theorem bounds_12_896 : exactInterval 12 896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_896 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 896) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_896 : oddCount 896 12 = 4 ∧ acceleratedOrbit 12 896 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_896 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 896) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_896.1, data_12_896.2]

/-- Complete interval computation for depth 12, residue 897. -/
theorem bounds_12_897 : exactInterval 12 897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_897 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 897) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_897 : oddCount 897 12 = 7 ∧ acceleratedOrbit 12 897 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_897 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 897) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_897.1, data_12_897.2]

/-- Complete interval computation for depth 12, residue 898. -/
theorem bounds_12_898 : exactInterval 12 898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_898 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 898) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_898 : oddCount 898 12 = 7 ∧ acceleratedOrbit 12 898 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_898 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 898) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_898.1, data_12_898.2]

/-- Complete interval computation for depth 12, residue 899. -/
theorem bounds_12_899 : exactInterval 12 899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_899 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 899) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_899 : oddCount 899 12 = 7 ∧ acceleratedOrbit 12 899 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_899 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 899) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_899.1, data_12_899.2]

/-- Complete interval computation for depth 12, residue 900. -/
theorem bounds_12_900 : exactInterval 12 900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_900 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 900) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_900 : oddCount 900 12 = 8 ∧ acceleratedOrbit 12 900 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_900 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 900) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_900.1, data_12_900.2]

/-- Complete interval computation for depth 12, residue 901. -/
theorem bounds_12_901 : exactInterval 12 901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_901 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 901) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_901 : oddCount 901 12 = 8 ∧ acceleratedOrbit 12 901 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_901 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 901) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_901.1, data_12_901.2]

/-- Complete interval computation for depth 12, residue 902. -/
theorem bounds_12_902 : exactInterval 12 902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_902 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 902) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_902 : oddCount 902 12 = 8 ∧ acceleratedOrbit 12 902 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_902 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 902) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_902.1, data_12_902.2]

/-- Complete interval computation for depth 12, residue 903. -/
theorem bounds_12_903 : exactInterval 12 903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_903 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 903) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_903 : oddCount 903 12 = 7 ∧ acceleratedOrbit 12 903 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_903 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 903) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_903.1, data_12_903.2]

/-- Complete interval computation for depth 12, residue 904. -/
theorem bounds_12_904 : exactInterval 12 904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_904 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 904) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_904 : oddCount 904 12 = 2 ∧ acceleratedOrbit 12 904 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_904 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 904) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_904.1, data_12_904.2]

/-- Complete interval computation for depth 12, residue 905. -/
theorem bounds_12_905 : exactInterval 12 905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_905 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 905) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_905 : oddCount 905 12 = 8 ∧ acceleratedOrbit 12 905 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_905 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 905) = 3 ^ 8 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_905.1, data_12_905.2]

end Collatz.Research.StoppingAtlas.Batch0259
