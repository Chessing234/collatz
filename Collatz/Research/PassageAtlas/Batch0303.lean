import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0303

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9895. -/
theorem bounds_15_9895 : exactInterval 15 9895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9895 : oddCount 9895 15 = 8 ∧ acceleratedOrbit 15 9895 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9895) = 3 ^ 8 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9895.1, data_15_9895.2]

/-- Complete interval computation for depth 15, residue 9896. -/
theorem bounds_15_9896 : exactInterval 15 9896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9896 : oddCount 9896 15 = 4 ∧ acceleratedOrbit 15 9896 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9896) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9896.1, data_15_9896.2]

/-- Complete interval computation for depth 15, residue 9897. -/
theorem bounds_15_9897 : exactInterval 15 9897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9897 : oddCount 9897 15 = 12 ∧ acceleratedOrbit 15 9897 = 160541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9897) = 3 ^ 12 * m + 160541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9897.1, data_15_9897.2]

/-- Complete interval computation for depth 15, residue 9898. -/
theorem bounds_15_9898 : exactInterval 15 9898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9898 : oddCount 9898 15 = 4 ∧ acceleratedOrbit 15 9898 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9898) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9898.1, data_15_9898.2]

/-- Complete interval computation for depth 15, residue 9899. -/
theorem bounds_15_9899 : exactInterval 15 9899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9899 : oddCount 9899 15 = 10 ∧ acceleratedOrbit 15 9899 = 17846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9899) = 3 ^ 10 * m + 17846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9899.1, data_15_9899.2]

/-- Complete interval computation for depth 15, residue 9900. -/
theorem bounds_15_9900 : exactInterval 15 9900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9900 : oddCount 9900 15 = 9 ∧ acceleratedOrbit 15 9900 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9900) = 3 ^ 9 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9900.1, data_15_9900.2]

/-- Complete interval computation for depth 15, residue 9901. -/
theorem bounds_15_9901 : exactInterval 15 9901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9901 : oddCount 9901 15 = 9 ∧ acceleratedOrbit 15 9901 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9901) = 3 ^ 9 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9901.1, data_15_9901.2]

/-- Complete interval computation for depth 15, residue 9902. -/
theorem bounds_15_9902 : exactInterval 15 9902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9902 : oddCount 9902 15 = 9 ∧ acceleratedOrbit 15 9902 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9902) = 3 ^ 9 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9902.1, data_15_9902.2]

/-- Complete interval computation for depth 15, residue 9903. -/
theorem bounds_15_9903 : exactInterval 15 9903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9903 : oddCount 9903 15 = 9 ∧ acceleratedOrbit 15 9903 = 5950 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9903) = 3 ^ 9 * m + 5950 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9903.1, data_15_9903.2]

/-- Complete interval computation for depth 15, residue 9904. -/
theorem bounds_15_9904 : exactInterval 15 9904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9904 : oddCount 9904 15 = 6 ∧ acceleratedOrbit 15 9904 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9904) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9904.1, data_15_9904.2]

/-- Complete interval computation for depth 15, residue 9905. -/
theorem bounds_15_9905 : exactInterval 15 9905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9905 : oddCount 9905 15 = 5 ∧ acceleratedOrbit 15 9905 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9905) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9905.1, data_15_9905.2]

/-- Complete interval computation for depth 15, residue 9906. -/
theorem bounds_15_9906 : exactInterval 15 9906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9906 : oddCount 9906 15 = 5 ∧ acceleratedOrbit 15 9906 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9906) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9906.1, data_15_9906.2]

/-- Complete interval computation for depth 15, residue 9907. -/
theorem bounds_15_9907 : exactInterval 15 9907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9907 : oddCount 9907 15 = 5 ∧ acceleratedOrbit 15 9907 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9907) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9907.1, data_15_9907.2]

/-- Complete interval computation for depth 15, residue 9908. -/
theorem bounds_15_9908 : exactInterval 15 9908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9908 : oddCount 9908 15 = 6 ∧ acceleratedOrbit 15 9908 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9908) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9908.1, data_15_9908.2]

/-- Complete interval computation for depth 15, residue 9909. -/
theorem bounds_15_9909 : exactInterval 15 9909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9909 : oddCount 9909 15 = 6 ∧ acceleratedOrbit 15 9909 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9909) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9909.1, data_15_9909.2]

/-- Complete interval computation for depth 15, residue 9910. -/
theorem bounds_15_9910 : exactInterval 15 9910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9910 : oddCount 9910 15 = 8 ∧ acceleratedOrbit 15 9910 = 1985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9910) = 3 ^ 8 * m + 1985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9910.1, data_15_9910.2]

/-- Complete interval computation for depth 15, residue 9911. -/
theorem bounds_15_9911 : exactInterval 15 9911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9911 : oddCount 9911 15 = 8 ∧ acceleratedOrbit 15 9911 = 1985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9911) = 3 ^ 8 * m + 1985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9911.1, data_15_9911.2]

/-- Complete interval computation for depth 15, residue 9912. -/
theorem bounds_15_9912 : exactInterval 15 9912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9912 : oddCount 9912 15 = 6 ∧ acceleratedOrbit 15 9912 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9912) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9912.1, data_15_9912.2]

/-- Complete interval computation for depth 15, residue 9913. -/
theorem bounds_15_9913 : exactInterval 15 9913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9913 : oddCount 9913 15 = 7 ∧ acceleratedOrbit 15 9913 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9913) = 3 ^ 7 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9913.1, data_15_9913.2]

/-- Complete interval computation for depth 15, residue 9914. -/
theorem bounds_15_9914 : exactInterval 15 9914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9914 : oddCount 9914 15 = 6 ∧ acceleratedOrbit 15 9914 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9914) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9914.1, data_15_9914.2]

/-- Complete interval computation for depth 15, residue 9915. -/
theorem bounds_15_9915 : exactInterval 15 9915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9915 : oddCount 9915 15 = 7 ∧ acceleratedOrbit 15 9915 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9915) = 3 ^ 7 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9915.1, data_15_9915.2]

/-- Complete interval computation for depth 15, residue 9916. -/
theorem bounds_15_9916 : exactInterval 15 9916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9916 : oddCount 9916 15 = 8 ∧ acceleratedOrbit 15 9916 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9916) = 3 ^ 8 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9916.1, data_15_9916.2]

/-- Complete interval computation for depth 15, residue 9917. -/
theorem bounds_15_9917 : exactInterval 15 9917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9917 : oddCount 9917 15 = 8 ∧ acceleratedOrbit 15 9917 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9917) = 3 ^ 8 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9917.1, data_15_9917.2]

/-- Complete interval computation for depth 15, residue 9918. -/
theorem bounds_15_9918 : exactInterval 15 9918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9918 : oddCount 9918 15 = 8 ∧ acceleratedOrbit 15 9918 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9918) = 3 ^ 8 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9918.1, data_15_9918.2]

/-- Complete interval computation for depth 15, residue 9919. -/
theorem bounds_15_9919 : exactInterval 15 9919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9919 : oddCount 9919 15 = 9 ∧ acceleratedOrbit 15 9919 = 5959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9919) = 3 ^ 9 * m + 5959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9919.1, data_15_9919.2]

/-- Complete interval computation for depth 15, residue 9920. -/
theorem bounds_15_9920 : exactInterval 15 9920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9920 : oddCount 9920 15 = 7 ∧ acceleratedOrbit 15 9920 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9920) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9920.1, data_15_9920.2]

/-- Complete interval computation for depth 15, residue 9921. -/
theorem bounds_15_9921 : exactInterval 15 9921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9921 : oddCount 9921 15 = 6 ∧ acceleratedOrbit 15 9921 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9921) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9921.1, data_15_9921.2]

/-- Complete interval computation for depth 15, residue 9922. -/
theorem bounds_15_9922 : exactInterval 15 9922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9922 : oddCount 9922 15 = 10 ∧ acceleratedOrbit 15 9922 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9922) = 3 ^ 10 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9922.1, data_15_9922.2]

/-- Complete interval computation for depth 15, residue 9923. -/
theorem bounds_15_9923 : exactInterval 15 9923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9923 : oddCount 9923 15 = 10 ∧ acceleratedOrbit 15 9923 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9923) = 3 ^ 10 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9923.1, data_15_9923.2]

/-- Complete interval computation for depth 15, residue 9924. -/
theorem bounds_15_9924 : exactInterval 15 9924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9924 : oddCount 9924 15 = 5 ∧ acceleratedOrbit 15 9924 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9924) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9924.1, data_15_9924.2]

/-- Complete interval computation for depth 15, residue 9925. -/
theorem bounds_15_9925 : exactInterval 15 9925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9925 : oddCount 9925 15 = 5 ∧ acceleratedOrbit 15 9925 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9925) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9925.1, data_15_9925.2]

/-- Complete interval computation for depth 15, residue 9926. -/
theorem bounds_15_9926 : exactInterval 15 9926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9926 : oddCount 9926 15 = 5 ∧ acceleratedOrbit 15 9926 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9926) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9926.1, data_15_9926.2]

/-- Complete interval computation for depth 15, residue 9927. -/
theorem bounds_15_9927 : exactInterval 15 9927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9927 : oddCount 9927 15 = 6 ∧ acceleratedOrbit 15 9927 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9927) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9927.1, data_15_9927.2]

end Collatz.Research.PassageAtlas.Batch0303
