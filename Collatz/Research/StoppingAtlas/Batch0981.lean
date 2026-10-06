import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0981

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7884. -/
theorem bounds_13_7884 : exactInterval 13 7884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7884 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7884) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7884 : oddCount 7884 13 = 3 ∧ acceleratedOrbit 13 7884 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7884 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7884) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7884.1, data_13_7884.2]

/-- Complete interval computation for depth 13, residue 7885. -/
theorem bounds_13_7885 : exactInterval 13 7885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7885 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7885) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7885 : oddCount 7885 13 = 3 ∧ acceleratedOrbit 13 7885 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7885 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7885) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7885.1, data_13_7885.2]

/-- Complete interval computation for depth 13, residue 7886. -/
theorem bounds_13_7886 : exactInterval 13 7886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7886 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7886) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7886 : oddCount 7886 13 = 11 ∧ acceleratedOrbit 13 7886 = 170585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7886 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7886) = 3 ^ 11 * m + 170585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7886.1, data_13_7886.2]

/-- Complete interval computation for depth 13, residue 7887. -/
theorem bounds_13_7887 : exactInterval 13 7887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7887 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7887) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7887 : oddCount 7887 13 = 11 ∧ acceleratedOrbit 13 7887 = 170585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7887 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7887) = 3 ^ 11 * m + 170585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7887.1, data_13_7887.2]

/-- Complete interval computation for depth 13, residue 7888. -/
theorem bounds_13_7888 : exactInterval 13 7888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7888 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7888) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7888 : oddCount 7888 13 = 5 ∧ acceleratedOrbit 13 7888 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7888 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7888) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7888.1, data_13_7888.2]

/-- Complete interval computation for depth 13, residue 7889. -/
theorem bounds_13_7889 : exactInterval 13 7889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7889 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7889) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7889 : oddCount 7889 13 = 7 ∧ acceleratedOrbit 13 7889 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7889 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7889) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7889.1, data_13_7889.2]

/-- Complete interval computation for depth 13, residue 7890. -/
theorem bounds_13_7890 : exactInterval 13 7890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7890 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7890) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7890 : oddCount 7890 13 = 7 ∧ acceleratedOrbit 13 7890 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7890 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7890) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7890.1, data_13_7890.2]

/-- Complete interval computation for depth 13, residue 7891. -/
theorem bounds_13_7891 : exactInterval 13 7891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7891 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7891) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7891 : oddCount 7891 13 = 7 ∧ acceleratedOrbit 13 7891 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7891 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7891) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7891.1, data_13_7891.2]

/-- Complete interval computation for depth 13, residue 7892. -/
theorem bounds_13_7892 : exactInterval 13 7892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7892 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7892) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7892 : oddCount 7892 13 = 5 ∧ acceleratedOrbit 13 7892 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7892 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7892) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7892.1, data_13_7892.2]

/-- Complete interval computation for depth 13, residue 7893. -/
theorem bounds_13_7893 : exactInterval 13 7893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7893 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7893) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7893 : oddCount 7893 13 = 5 ∧ acceleratedOrbit 13 7893 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7893 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7893) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7893.1, data_13_7893.2]

/-- Complete interval computation for depth 13, residue 7894. -/
theorem bounds_13_7894 : exactInterval 13 7894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7894 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7894) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7894 : oddCount 7894 13 = 6 ∧ acceleratedOrbit 13 7894 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7894 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7894) = 3 ^ 6 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7894.1, data_13_7894.2]

/-- Complete interval computation for depth 13, residue 7895. -/
theorem bounds_13_7895 : exactInterval 13 7895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7895 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7895) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7895 : oddCount 7895 13 = 6 ∧ acceleratedOrbit 13 7895 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7895 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7895) = 3 ^ 6 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7895.1, data_13_7895.2]

/-- Complete interval computation for depth 13, residue 7896. -/
theorem bounds_13_7896 : exactInterval 13 7896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7896 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7896) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7896 : oddCount 7896 13 = 6 ∧ acceleratedOrbit 13 7896 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7896 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7896) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7896.1, data_13_7896.2]

/-- Complete interval computation for depth 13, residue 7897. -/
theorem bounds_13_7897 : exactInterval 13 7897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7897 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7897) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7897 : oddCount 7897 13 = 6 ∧ acceleratedOrbit 13 7897 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7897 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7897) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7897.1, data_13_7897.2]

/-- Complete interval computation for depth 13, residue 7898. -/
theorem bounds_13_7898 : exactInterval 13 7898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7898 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7898) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7898 : oddCount 7898 13 = 6 ∧ acceleratedOrbit 13 7898 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7898 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7898) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7898.1, data_13_7898.2]

/-- Complete interval computation for depth 13, residue 7899. -/
theorem bounds_13_7899 : exactInterval 13 7899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7899 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7899) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7899 : oddCount 7899 13 = 8 ∧ acceleratedOrbit 13 7899 = 6328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7899 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7899) = 3 ^ 8 * m + 6328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7899.1, data_13_7899.2]

end Collatz.Research.StoppingAtlas.Batch0981
