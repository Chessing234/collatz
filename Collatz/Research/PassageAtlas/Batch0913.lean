import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0913

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29884. -/
theorem bounds_15_29884 : exactInterval 15 29884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29884 : oddCount 29884 15 = 10 ∧ acceleratedOrbit 15 29884 = 53864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29884) = 3 ^ 10 * m + 53864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29884.1, data_15_29884.2]

/-- Complete interval computation for depth 15, residue 29885. -/
theorem bounds_15_29885 : exactInterval 15 29885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29885 : oddCount 29885 15 = 10 ∧ acceleratedOrbit 15 29885 = 53864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29885) = 3 ^ 10 * m + 53864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29885.1, data_15_29885.2]

/-- Complete interval computation for depth 15, residue 29886. -/
theorem bounds_15_29886 : exactInterval 15 29886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29886 : oddCount 29886 15 = 10 ∧ acceleratedOrbit 15 29886 = 53864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29886) = 3 ^ 10 * m + 53864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29886.1, data_15_29886.2]

/-- Complete interval computation for depth 15, residue 29887. -/
theorem bounds_15_29887 : exactInterval 15 29887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29887 : oddCount 29887 15 = 10 ∧ acceleratedOrbit 15 29887 = 53860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29887) = 3 ^ 10 * m + 53860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29887.1, data_15_29887.2]

/-- Complete interval computation for depth 15, residue 29888. -/
theorem bounds_15_29888 : exactInterval 15 29888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29888 : oddCount 29888 15 = 6 ∧ acceleratedOrbit 15 29888 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29888) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29888.1, data_15_29888.2]

/-- Complete interval computation for depth 15, residue 29889. -/
theorem bounds_15_29889 : exactInterval 15 29889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29889 : oddCount 29889 15 = 8 ∧ acceleratedOrbit 15 29889 = 5987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29889) = 3 ^ 8 * m + 5987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29889.1, data_15_29889.2]

/-- Complete interval computation for depth 15, residue 29890. -/
theorem bounds_15_29890 : exactInterval 15 29890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29890 : oddCount 29890 15 = 8 ∧ acceleratedOrbit 15 29890 = 5987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29890) = 3 ^ 8 * m + 5987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29890.1, data_15_29890.2]

/-- Complete interval computation for depth 15, residue 29891. -/
theorem bounds_15_29891 : exactInterval 15 29891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29891 : oddCount 29891 15 = 8 ∧ acceleratedOrbit 15 29891 = 5987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29891) = 3 ^ 8 * m + 5987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29891.1, data_15_29891.2]

/-- Complete interval computation for depth 15, residue 29892. -/
theorem bounds_15_29892 : exactInterval 15 29892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29892 : oddCount 29892 15 = 8 ∧ acceleratedOrbit 15 29892 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29892) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29892.1, data_15_29892.2]

/-- Complete interval computation for depth 15, residue 29893. -/
theorem bounds_15_29893 : exactInterval 15 29893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29893 : oddCount 29893 15 = 8 ∧ acceleratedOrbit 15 29893 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29893) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29893.1, data_15_29893.2]

/-- Complete interval computation for depth 15, residue 29894. -/
theorem bounds_15_29894 : exactInterval 15 29894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29894 : oddCount 29894 15 = 8 ∧ acceleratedOrbit 15 29894 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29894) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29894.1, data_15_29894.2]

/-- Complete interval computation for depth 15, residue 29895. -/
theorem bounds_15_29895 : exactInterval 15 29895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29895 : oddCount 29895 15 = 8 ∧ acceleratedOrbit 15 29895 = 5987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29895) = 3 ^ 8 * m + 5987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29895.1, data_15_29895.2]

/-- Complete interval computation for depth 15, residue 29896. -/
theorem bounds_15_29896 : exactInterval 15 29896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29896 : oddCount 29896 15 = 8 ∧ acceleratedOrbit 15 29896 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29896) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29896.1, data_15_29896.2]

/-- Complete interval computation for depth 15, residue 29897. -/
theorem bounds_15_29897 : exactInterval 15 29897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29897 : oddCount 29897 15 = 7 ∧ acceleratedOrbit 15 29897 = 1997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29897) = 3 ^ 7 * m + 1997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29897.1, data_15_29897.2]

/-- Complete interval computation for depth 15, residue 29898. -/
theorem bounds_15_29898 : exactInterval 15 29898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29898 : oddCount 29898 15 = 8 ∧ acceleratedOrbit 15 29898 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29898) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29898.1, data_15_29898.2]

/-- Complete interval computation for depth 15, residue 29899. -/
theorem bounds_15_29899 : exactInterval 15 29899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29899 : oddCount 29899 15 = 7 ∧ acceleratedOrbit 15 29899 = 1997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29899) = 3 ^ 7 * m + 1997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29899.1, data_15_29899.2]

/-- Complete interval computation for depth 15, residue 29900. -/
theorem bounds_15_29900 : exactInterval 15 29900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29900 : oddCount 29900 15 = 8 ∧ acceleratedOrbit 15 29900 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29900) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29900.1, data_15_29900.2]

/-- Complete interval computation for depth 15, residue 29901. -/
theorem bounds_15_29901 : exactInterval 15 29901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29901 : oddCount 29901 15 = 8 ∧ acceleratedOrbit 15 29901 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29901) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29901.1, data_15_29901.2]

/-- Complete interval computation for depth 15, residue 29902. -/
theorem bounds_15_29902 : exactInterval 15 29902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29902 : oddCount 29902 15 = 10 ∧ acceleratedOrbit 15 29902 = 53891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29902) = 3 ^ 10 * m + 53891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29902.1, data_15_29902.2]

/-- Complete interval computation for depth 15, residue 29903. -/
theorem bounds_15_29903 : exactInterval 15 29903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29903 : oddCount 29903 15 = 10 ∧ acceleratedOrbit 15 29903 = 53891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29903) = 3 ^ 10 * m + 53891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29903.1, data_15_29903.2]

/-- Complete interval computation for depth 15, residue 29904. -/
theorem bounds_15_29904 : exactInterval 15 29904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29904 : oddCount 29904 15 = 6 ∧ acceleratedOrbit 15 29904 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29904) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29904.1, data_15_29904.2]

/-- Complete interval computation for depth 15, residue 29905. -/
theorem bounds_15_29905 : exactInterval 15 29905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29905 : oddCount 29905 15 = 8 ∧ acceleratedOrbit 15 29905 = 5989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29905) = 3 ^ 8 * m + 5989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29905.1, data_15_29905.2]

/-- Complete interval computation for depth 15, residue 29906. -/
theorem bounds_15_29906 : exactInterval 15 29906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29906 : oddCount 29906 15 = 8 ∧ acceleratedOrbit 15 29906 = 5989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29906) = 3 ^ 8 * m + 5989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29906.1, data_15_29906.2]

/-- Complete interval computation for depth 15, residue 29907. -/
theorem bounds_15_29907 : exactInterval 15 29907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29907 : oddCount 29907 15 = 8 ∧ acceleratedOrbit 15 29907 = 5989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29907) = 3 ^ 8 * m + 5989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29907.1, data_15_29907.2]

/-- Complete interval computation for depth 15, residue 29908. -/
theorem bounds_15_29908 : exactInterval 15 29908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29908 : oddCount 29908 15 = 6 ∧ acceleratedOrbit 15 29908 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29908) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29908.1, data_15_29908.2]

/-- Complete interval computation for depth 15, residue 29909. -/
theorem bounds_15_29909 : exactInterval 15 29909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29909 : oddCount 29909 15 = 6 ∧ acceleratedOrbit 15 29909 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29909) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29909.1, data_15_29909.2]

/-- Complete interval computation for depth 15, residue 29910. -/
theorem bounds_15_29910 : exactInterval 15 29910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29910 : oddCount 29910 15 = 7 ∧ acceleratedOrbit 15 29910 = 1997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29910) = 3 ^ 7 * m + 1997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29910.1, data_15_29910.2]

/-- Complete interval computation for depth 15, residue 29911. -/
theorem bounds_15_29911 : exactInterval 15 29911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29911 : oddCount 29911 15 = 7 ∧ acceleratedOrbit 15 29911 = 1997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29911) = 3 ^ 7 * m + 1997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29911.1, data_15_29911.2]

/-- Complete interval computation for depth 15, residue 29912. -/
theorem bounds_15_29912 : exactInterval 15 29912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29912 : oddCount 29912 15 = 9 ∧ acceleratedOrbit 15 29912 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29912) = 3 ^ 9 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29912.1, data_15_29912.2]

/-- Complete interval computation for depth 15, residue 29913. -/
theorem bounds_15_29913 : exactInterval 15 29913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29913 : oddCount 29913 15 = 8 ∧ acceleratedOrbit 15 29913 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29913) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29913.1, data_15_29913.2]

/-- Complete interval computation for depth 15, residue 29914. -/
theorem bounds_15_29914 : exactInterval 15 29914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29914 : oddCount 29914 15 = 9 ∧ acceleratedOrbit 15 29914 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29914) = 3 ^ 9 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29914.1, data_15_29914.2]

/-- Complete interval computation for depth 15, residue 29915. -/
theorem bounds_15_29915 : exactInterval 15 29915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29915 : oddCount 29915 15 = 9 ∧ acceleratedOrbit 15 29915 = 17972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29915) = 3 ^ 9 * m + 17972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29915.1, data_15_29915.2]

/-- Complete interval computation for depth 15, residue 29916. -/
theorem bounds_15_29916 : exactInterval 15 29916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29916 : oddCount 29916 15 = 9 ∧ acceleratedOrbit 15 29916 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29916) = 3 ^ 9 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29916.1, data_15_29916.2]

end Collatz.Research.PassageAtlas.Batch0913
