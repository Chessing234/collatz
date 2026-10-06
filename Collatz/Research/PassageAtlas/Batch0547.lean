import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0547

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17891. -/
theorem bounds_15_17891 : exactInterval 15 17891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17891 : oddCount 17891 15 = 5 ∧ acceleratedOrbit 15 17891 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17891) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17891.1, data_15_17891.2]

/-- Complete interval computation for depth 15, residue 17892. -/
theorem bounds_15_17892 : exactInterval 15 17892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17892 : oddCount 17892 15 = 10 ∧ acceleratedOrbit 15 17892 = 32258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17892) = 3 ^ 10 * m + 32258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17892.1, data_15_17892.2]

/-- Complete interval computation for depth 15, residue 17893. -/
theorem bounds_15_17893 : exactInterval 15 17893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17893 : oddCount 17893 15 = 10 ∧ acceleratedOrbit 15 17893 = 32258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17893) = 3 ^ 10 * m + 32258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17893.1, data_15_17893.2]

/-- Complete interval computation for depth 15, residue 17894. -/
theorem bounds_15_17894 : exactInterval 15 17894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17894 : oddCount 17894 15 = 10 ∧ acceleratedOrbit 15 17894 = 32258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17894) = 3 ^ 10 * m + 32258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17894.1, data_15_17894.2]

/-- Complete interval computation for depth 15, residue 17895. -/
theorem bounds_15_17895 : exactInterval 15 17895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17895 : oddCount 17895 15 = 10 ∧ acceleratedOrbit 15 17895 = 32251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17895) = 3 ^ 10 * m + 32251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17895.1, data_15_17895.2]

/-- Complete interval computation for depth 15, residue 17896. -/
theorem bounds_15_17896 : exactInterval 15 17896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17896 : oddCount 17896 15 = 8 ∧ acceleratedOrbit 15 17896 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17896) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17896.1, data_15_17896.2]

/-- Complete interval computation for depth 15, residue 17897. -/
theorem bounds_15_17897 : exactInterval 15 17897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17897 : oddCount 17897 15 = 10 ∧ acceleratedOrbit 15 17897 = 32255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17897) = 3 ^ 10 * m + 32255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17897.1, data_15_17897.2]

/-- Complete interval computation for depth 15, residue 17898. -/
theorem bounds_15_17898 : exactInterval 15 17898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17898 : oddCount 17898 15 = 8 ∧ acceleratedOrbit 15 17898 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17898) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17898.1, data_15_17898.2]

/-- Complete interval computation for depth 15, residue 17899. -/
theorem bounds_15_17899 : exactInterval 15 17899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17899 : oddCount 17899 15 = 12 ∧ acceleratedOrbit 15 17899 = 290324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17899) = 3 ^ 12 * m + 290324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17899.1, data_15_17899.2]

/-- Complete interval computation for depth 15, residue 17900. -/
theorem bounds_15_17900 : exactInterval 15 17900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17900 : oddCount 17900 15 = 8 ∧ acceleratedOrbit 15 17900 = 3586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17900) = 3 ^ 8 * m + 3586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17900.1, data_15_17900.2]

/-- Complete interval computation for depth 15, residue 17901. -/
theorem bounds_15_17901 : exactInterval 15 17901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17901 : oddCount 17901 15 = 8 ∧ acceleratedOrbit 15 17901 = 3586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17901) = 3 ^ 8 * m + 3586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17901.1, data_15_17901.2]

/-- Complete interval computation for depth 15, residue 17902. -/
theorem bounds_15_17902 : exactInterval 15 17902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17902 : oddCount 17902 15 = 8 ∧ acceleratedOrbit 15 17902 = 3586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17902) = 3 ^ 8 * m + 3586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17902.1, data_15_17902.2]

/-- Complete interval computation for depth 15, residue 17903. -/
theorem bounds_15_17903 : exactInterval 15 17903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17903 : oddCount 17903 15 = 11 ∧ acceleratedOrbit 15 17903 = 96794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17903) = 3 ^ 11 * m + 96794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17903.1, data_15_17903.2]

/-- Complete interval computation for depth 15, residue 17904. -/
theorem bounds_15_17904 : exactInterval 15 17904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17904 : oddCount 17904 15 = 8 ∧ acceleratedOrbit 15 17904 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17904) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17904.1, data_15_17904.2]

/-- Complete interval computation for depth 15, residue 17905. -/
theorem bounds_15_17905 : exactInterval 15 17905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17905 : oddCount 17905 15 = 8 ∧ acceleratedOrbit 15 17905 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17905) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17905.1, data_15_17905.2]

/-- Complete interval computation for depth 15, residue 17906. -/
theorem bounds_15_17906 : exactInterval 15 17906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17906 : oddCount 17906 15 = 7 ∧ acceleratedOrbit 15 17906 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17906) = 3 ^ 7 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17906.1, data_15_17906.2]

/-- Complete interval computation for depth 15, residue 17907. -/
theorem bounds_15_17907 : exactInterval 15 17907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17907 : oddCount 17907 15 = 7 ∧ acceleratedOrbit 15 17907 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17907) = 3 ^ 7 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17907.1, data_15_17907.2]

/-- Complete interval computation for depth 15, residue 17908. -/
theorem bounds_15_17908 : exactInterval 15 17908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17908 : oddCount 17908 15 = 8 ∧ acceleratedOrbit 15 17908 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17908) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17908.1, data_15_17908.2]

/-- Complete interval computation for depth 15, residue 17909. -/
theorem bounds_15_17909 : exactInterval 15 17909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17909 : oddCount 17909 15 = 8 ∧ acceleratedOrbit 15 17909 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17909) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17909.1, data_15_17909.2]

/-- Complete interval computation for depth 15, residue 17910. -/
theorem bounds_15_17910 : exactInterval 15 17910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17910 : oddCount 17910 15 = 10 ∧ acceleratedOrbit 15 17910 = 32282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17910) = 3 ^ 10 * m + 32282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17910.1, data_15_17910.2]

/-- Complete interval computation for depth 15, residue 17911. -/
theorem bounds_15_17911 : exactInterval 15 17911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17911 : oddCount 17911 15 = 10 ∧ acceleratedOrbit 15 17911 = 32282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17911) = 3 ^ 10 * m + 32282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17911.1, data_15_17911.2]

/-- Complete interval computation for depth 15, residue 17912. -/
theorem bounds_15_17912 : exactInterval 15 17912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17912 : oddCount 17912 15 = 7 ∧ acceleratedOrbit 15 17912 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17912) = 3 ^ 7 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17912.1, data_15_17912.2]

/-- Complete interval computation for depth 15, residue 17913. -/
theorem bounds_15_17913 : exactInterval 15 17913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17913 : oddCount 17913 15 = 9 ∧ acceleratedOrbit 15 17913 = 10763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17913) = 3 ^ 9 * m + 10763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17913.1, data_15_17913.2]

/-- Complete interval computation for depth 15, residue 17914. -/
theorem bounds_15_17914 : exactInterval 15 17914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17914 : oddCount 17914 15 = 7 ∧ acceleratedOrbit 15 17914 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17914) = 3 ^ 7 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17914.1, data_15_17914.2]

/-- Complete interval computation for depth 15, residue 17915. -/
theorem bounds_15_17915 : exactInterval 15 17915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17915 : oddCount 17915 15 = 9 ∧ acceleratedOrbit 15 17915 = 10763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17915) = 3 ^ 9 * m + 10763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17915.1, data_15_17915.2]

/-- Complete interval computation for depth 15, residue 17916. -/
theorem bounds_15_17916 : exactInterval 15 17916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17916 : oddCount 17916 15 = 7 ∧ acceleratedOrbit 15 17916 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17916) = 3 ^ 7 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17916.1, data_15_17916.2]

/-- Complete interval computation for depth 15, residue 17917. -/
theorem bounds_15_17917 : exactInterval 15 17917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17917 : oddCount 17917 15 = 7 ∧ acceleratedOrbit 15 17917 = 1196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17917) = 3 ^ 7 * m + 1196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17917.1, data_15_17917.2]

/-- Complete interval computation for depth 15, residue 17918. -/
theorem bounds_15_17918 : exactInterval 15 17918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17918 : oddCount 17918 15 = 11 ∧ acceleratedOrbit 15 17918 = 96878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17918) = 3 ^ 11 * m + 96878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17918.1, data_15_17918.2]

/-- Complete interval computation for depth 15, residue 17919. -/
theorem bounds_15_17919 : exactInterval 15 17919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17919 : oddCount 17919 15 = 11 ∧ acceleratedOrbit 15 17919 = 96878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17919) = 3 ^ 11 * m + 96878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17919.1, data_15_17919.2]

/-- Complete interval computation for depth 15, residue 17920. -/
theorem bounds_15_17920 : exactInterval 15 17920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17920 : oddCount 17920 15 = 2 ∧ acceleratedOrbit 15 17920 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17920) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17920.1, data_15_17920.2]

/-- Complete interval computation for depth 15, residue 17921. -/
theorem bounds_15_17921 : exactInterval 15 17921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17921 : oddCount 17921 15 = 9 ∧ acceleratedOrbit 15 17921 = 10768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17921) = 3 ^ 9 * m + 10768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17921.1, data_15_17921.2]

/-- Complete interval computation for depth 15, residue 17922. -/
theorem bounds_15_17922 : exactInterval 15 17922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17922 : oddCount 17922 15 = 5 ∧ acceleratedOrbit 15 17922 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17922) = 3 ^ 5 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17922.1, data_15_17922.2]

/-- Complete interval computation for depth 15, residue 17923. -/
theorem bounds_15_17923 : exactInterval 15 17923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17923 : oddCount 17923 15 = 5 ∧ acceleratedOrbit 15 17923 = 133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17923) = 3 ^ 5 * m + 133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17923.1, data_15_17923.2]

end Collatz.Research.PassageAtlas.Batch0547
