import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0974

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31883. -/
theorem bounds_15_31883 : exactInterval 15 31883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31883 : oddCount 31883 15 = 8 ∧ acceleratedOrbit 15 31883 = 6385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31883) = 3 ^ 8 * m + 6385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31883.1, data_15_31883.2]

/-- Complete interval computation for depth 15, residue 31884. -/
theorem bounds_15_31884 : exactInterval 15 31884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31884 : oddCount 31884 15 = 7 ∧ acceleratedOrbit 15 31884 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31884) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31884.1, data_15_31884.2]

/-- Complete interval computation for depth 15, residue 31885. -/
theorem bounds_15_31885 : exactInterval 15 31885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31885 : oddCount 31885 15 = 7 ∧ acceleratedOrbit 15 31885 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31885) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31885.1, data_15_31885.2]

/-- Complete interval computation for depth 15, residue 31886. -/
theorem bounds_15_31886 : exactInterval 15 31886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31886 : oddCount 31886 15 = 9 ∧ acceleratedOrbit 15 31886 = 19156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31886) = 3 ^ 9 * m + 19156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31886.1, data_15_31886.2]

/-- Complete interval computation for depth 15, residue 31887. -/
theorem bounds_15_31887 : exactInterval 15 31887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31887 : oddCount 31887 15 = 9 ∧ acceleratedOrbit 15 31887 = 19156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31887) = 3 ^ 9 * m + 19156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31887.1, data_15_31887.2]

/-- Complete interval computation for depth 15, residue 31888. -/
theorem bounds_15_31888 : exactInterval 15 31888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31888 : oddCount 31888 15 = 7 ∧ acceleratedOrbit 15 31888 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31888) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31888.1, data_15_31888.2]

/-- Complete interval computation for depth 15, residue 31889. -/
theorem bounds_15_31889 : exactInterval 15 31889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31889 : oddCount 31889 15 = 9 ∧ acceleratedOrbit 15 31889 = 19160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31889) = 3 ^ 9 * m + 19160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31889.1, data_15_31889.2]

/-- Complete interval computation for depth 15, residue 31890. -/
theorem bounds_15_31890 : exactInterval 15 31890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31890 : oddCount 31890 15 = 9 ∧ acceleratedOrbit 15 31890 = 19160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31890) = 3 ^ 9 * m + 19160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31890.1, data_15_31890.2]

/-- Complete interval computation for depth 15, residue 31891. -/
theorem bounds_15_31891 : exactInterval 15 31891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31891 : oddCount 31891 15 = 9 ∧ acceleratedOrbit 15 31891 = 19160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31891) = 3 ^ 9 * m + 19160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31891.1, data_15_31891.2]

/-- Complete interval computation for depth 15, residue 31892. -/
theorem bounds_15_31892 : exactInterval 15 31892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31892 : oddCount 31892 15 = 7 ∧ acceleratedOrbit 15 31892 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31892) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31892.1, data_15_31892.2]

/-- Complete interval computation for depth 15, residue 31893. -/
theorem bounds_15_31893 : exactInterval 15 31893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31893 : oddCount 31893 15 = 7 ∧ acceleratedOrbit 15 31893 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31893) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31893.1, data_15_31893.2]

/-- Complete interval computation for depth 15, residue 31894. -/
theorem bounds_15_31894 : exactInterval 15 31894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31894 : oddCount 31894 15 = 7 ∧ acceleratedOrbit 15 31894 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31894) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31894.1, data_15_31894.2]

/-- Complete interval computation for depth 15, residue 31895. -/
theorem bounds_15_31895 : exactInterval 15 31895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31895 : oddCount 31895 15 = 7 ∧ acceleratedOrbit 15 31895 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31895) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31895.1, data_15_31895.2]

/-- Complete interval computation for depth 15, residue 31896. -/
theorem bounds_15_31896 : exactInterval 15 31896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31896 : oddCount 31896 15 = 7 ∧ acceleratedOrbit 15 31896 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31896) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31896.1, data_15_31896.2]

/-- Complete interval computation for depth 15, residue 31897. -/
theorem bounds_15_31897 : exactInterval 15 31897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31897 : oddCount 31897 15 = 8 ∧ acceleratedOrbit 15 31897 = 6389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31897) = 3 ^ 8 * m + 6389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31897.1, data_15_31897.2]

/-- Complete interval computation for depth 15, residue 31898. -/
theorem bounds_15_31898 : exactInterval 15 31898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31898 : oddCount 31898 15 = 7 ∧ acceleratedOrbit 15 31898 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31898) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31898.1, data_15_31898.2]

/-- Complete interval computation for depth 15, residue 31899. -/
theorem bounds_15_31899 : exactInterval 15 31899 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31899) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31899 : oddCount 31899 15 = 9 ∧ acceleratedOrbit 15 31899 = 19162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31899) = 3 ^ 9 * m + 19162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31899.1, data_15_31899.2]

/-- Complete interval computation for depth 15, residue 31900. -/
theorem bounds_15_31900 : exactInterval 15 31900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31900 : oddCount 31900 15 = 8 ∧ acceleratedOrbit 15 31900 = 6389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31900) = 3 ^ 8 * m + 6389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31900.1, data_15_31900.2]

/-- Complete interval computation for depth 15, residue 31901. -/
theorem bounds_15_31901 : exactInterval 15 31901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31901 : oddCount 31901 15 = 8 ∧ acceleratedOrbit 15 31901 = 6389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31901) = 3 ^ 8 * m + 6389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31901.1, data_15_31901.2]

/-- Complete interval computation for depth 15, residue 31902. -/
theorem bounds_15_31902 : exactInterval 15 31902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31902 : oddCount 31902 15 = 8 ∧ acceleratedOrbit 15 31902 = 6389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31902) = 3 ^ 8 * m + 6389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31902.1, data_15_31902.2]

/-- Complete interval computation for depth 15, residue 31903. -/
theorem bounds_15_31903 : exactInterval 15 31903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31903 : oddCount 31903 15 = 11 ∧ acceleratedOrbit 15 31903 = 172477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31903) = 3 ^ 11 * m + 172477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31903.1, data_15_31903.2]

/-- Complete interval computation for depth 15, residue 31904. -/
theorem bounds_15_31904 : exactInterval 15 31904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31904 : oddCount 31904 15 = 5 ∧ acceleratedOrbit 15 31904 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31904) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31904.1, data_15_31904.2]

/-- Complete interval computation for depth 15, residue 31905. -/
theorem bounds_15_31905 : exactInterval 15 31905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31905 : oddCount 31905 15 = 10 ∧ acceleratedOrbit 15 31905 = 57500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31905) = 3 ^ 10 * m + 57500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31905.1, data_15_31905.2]

/-- Complete interval computation for depth 15, residue 31906. -/
theorem bounds_15_31906 : exactInterval 15 31906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31906 : oddCount 31906 15 = 6 ∧ acceleratedOrbit 15 31906 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31906) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31906.1, data_15_31906.2]

/-- Complete interval computation for depth 15, residue 31907. -/
theorem bounds_15_31907 : exactInterval 15 31907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31907 : oddCount 31907 15 = 6 ∧ acceleratedOrbit 15 31907 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31907) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31907.1, data_15_31907.2]

/-- Complete interval computation for depth 15, residue 31908. -/
theorem bounds_15_31908 : exactInterval 15 31908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31908 : oddCount 31908 15 = 6 ∧ acceleratedOrbit 15 31908 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31908) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31908.1, data_15_31908.2]

/-- Complete interval computation for depth 15, residue 31909. -/
theorem bounds_15_31909 : exactInterval 15 31909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31909 : oddCount 31909 15 = 6 ∧ acceleratedOrbit 15 31909 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31909) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31909.1, data_15_31909.2]

/-- Complete interval computation for depth 15, residue 31910. -/
theorem bounds_15_31910 : exactInterval 15 31910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31910 : oddCount 31910 15 = 6 ∧ acceleratedOrbit 15 31910 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31910) = 3 ^ 6 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31910.1, data_15_31910.2]

/-- Complete interval computation for depth 15, residue 31911. -/
theorem bounds_15_31911 : exactInterval 15 31911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31911 : oddCount 31911 15 = 11 ∧ acceleratedOrbit 15 31911 = 172523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31911) = 3 ^ 11 * m + 172523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31911.1, data_15_31911.2]

/-- Complete interval computation for depth 15, residue 31912. -/
theorem bounds_15_31912 : exactInterval 15 31912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31912 : oddCount 31912 15 = 5 ∧ acceleratedOrbit 15 31912 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31912) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31912.1, data_15_31912.2]

/-- Complete interval computation for depth 15, residue 31913. -/
theorem bounds_15_31913 : exactInterval 15 31913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31913 : oddCount 31913 15 = 10 ∧ acceleratedOrbit 15 31913 = 57512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31913) = 3 ^ 10 * m + 57512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31913.1, data_15_31913.2]

/-- Complete interval computation for depth 15, residue 31914. -/
theorem bounds_15_31914 : exactInterval 15 31914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31914 : oddCount 31914 15 = 5 ∧ acceleratedOrbit 15 31914 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31914) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31914.1, data_15_31914.2]

/-- Complete interval computation for depth 15, residue 31915. -/
theorem bounds_15_31915 : exactInterval 15 31915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31915 : oddCount 31915 15 = 8 ∧ acceleratedOrbit 15 31915 = 6392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31915) = 3 ^ 8 * m + 6392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31915.1, data_15_31915.2]

end Collatz.Research.PassageAtlas.Batch0974
