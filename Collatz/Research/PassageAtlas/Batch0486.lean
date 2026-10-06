import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0486

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15892. -/
theorem bounds_15_15892 : exactInterval 15 15892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15892 : oddCount 15892 15 = 7 ∧ acceleratedOrbit 15 15892 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15892) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15892.1, data_15_15892.2]

/-- Complete interval computation for depth 15, residue 15893. -/
theorem bounds_15_15893 : exactInterval 15 15893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15893 : oddCount 15893 15 = 7 ∧ acceleratedOrbit 15 15893 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15893) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15893.1, data_15_15893.2]

/-- Complete interval computation for depth 15, residue 15894. -/
theorem bounds_15_15894 : exactInterval 15 15894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15894 : oddCount 15894 15 = 8 ∧ acceleratedOrbit 15 15894 = 3185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15894) = 3 ^ 8 * m + 3185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15894.1, data_15_15894.2]

/-- Complete interval computation for depth 15, residue 15895. -/
theorem bounds_15_15895 : exactInterval 15 15895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15895 : oddCount 15895 15 = 8 ∧ acceleratedOrbit 15 15895 = 3185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15895) = 3 ^ 8 * m + 3185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15895.1, data_15_15895.2]

/-- Complete interval computation for depth 15, residue 15896. -/
theorem bounds_15_15896 : exactInterval 15 15896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15896 : oddCount 15896 15 = 7 ∧ acceleratedOrbit 15 15896 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15896) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15896.1, data_15_15896.2]

/-- Complete interval computation for depth 15, residue 15897. -/
theorem bounds_15_15897 : exactInterval 15 15897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15897 : oddCount 15897 15 = 8 ∧ acceleratedOrbit 15 15897 = 3185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15897) = 3 ^ 8 * m + 3185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15897.1, data_15_15897.2]

/-- Complete interval computation for depth 15, residue 15898. -/
theorem bounds_15_15898 : exactInterval 15 15898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15898 : oddCount 15898 15 = 7 ∧ acceleratedOrbit 15 15898 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15898) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15898.1, data_15_15898.2]

/-- Complete interval computation for depth 15, residue 15899. -/
theorem bounds_15_15899 : exactInterval 15 15899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15899 : oddCount 15899 15 = 11 ∧ acceleratedOrbit 15 15899 = 85961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15899) = 3 ^ 11 * m + 85961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15899.1, data_15_15899.2]

/-- Complete interval computation for depth 15, residue 15900. -/
theorem bounds_15_15900 : exactInterval 15 15900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15900 : oddCount 15900 15 = 5 ∧ acceleratedOrbit 15 15900 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15900) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15900.1, data_15_15900.2]

/-- Complete interval computation for depth 15, residue 15901. -/
theorem bounds_15_15901 : exactInterval 15 15901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15901 : oddCount 15901 15 = 5 ∧ acceleratedOrbit 15 15901 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15901) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15901.1, data_15_15901.2]

/-- Complete interval computation for depth 15, residue 15902. -/
theorem bounds_15_15902 : exactInterval 15 15902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15902 : oddCount 15902 15 = 5 ∧ acceleratedOrbit 15 15902 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15902) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15902.1, data_15_15902.2]

/-- Complete interval computation for depth 15, residue 15903. -/
theorem bounds_15_15903 : exactInterval 15 15903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15903 : oddCount 15903 15 = 11 ∧ acceleratedOrbit 15 15903 = 85981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15903) = 3 ^ 11 * m + 85981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15903.1, data_15_15903.2]

/-- Complete interval computation for depth 15, residue 15904. -/
theorem bounds_15_15904 : exactInterval 15 15904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15904 : oddCount 15904 15 = 4 ∧ acceleratedOrbit 15 15904 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15904) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15904.1, data_15_15904.2]

/-- Complete interval computation for depth 15, residue 15905. -/
theorem bounds_15_15905 : exactInterval 15 15905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15905 : oddCount 15905 15 = 10 ∧ acceleratedOrbit 15 15905 = 28673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15905) = 3 ^ 10 * m + 28673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15905.1, data_15_15905.2]

/-- Complete interval computation for depth 15, residue 15906. -/
theorem bounds_15_15906 : exactInterval 15 15906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15906 : oddCount 15906 15 = 7 ∧ acceleratedOrbit 15 15906 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15906) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15906.1, data_15_15906.2]

/-- Complete interval computation for depth 15, residue 15907. -/
theorem bounds_15_15907 : exactInterval 15 15907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15907 : oddCount 15907 15 = 7 ∧ acceleratedOrbit 15 15907 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15907) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15907.1, data_15_15907.2]

/-- Complete interval computation for depth 15, residue 15908. -/
theorem bounds_15_15908 : exactInterval 15 15908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15908 : oddCount 15908 15 = 8 ∧ acceleratedOrbit 15 15908 = 3187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15908) = 3 ^ 8 * m + 3187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15908.1, data_15_15908.2]

/-- Complete interval computation for depth 15, residue 15909. -/
theorem bounds_15_15909 : exactInterval 15 15909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15909 : oddCount 15909 15 = 8 ∧ acceleratedOrbit 15 15909 = 3187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15909) = 3 ^ 8 * m + 3187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15909.1, data_15_15909.2]

/-- Complete interval computation for depth 15, residue 15910. -/
theorem bounds_15_15910 : exactInterval 15 15910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15910 : oddCount 15910 15 = 8 ∧ acceleratedOrbit 15 15910 = 3187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15910) = 3 ^ 8 * m + 3187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15910.1, data_15_15910.2]

/-- Complete interval computation for depth 15, residue 15911. -/
theorem bounds_15_15911 : exactInterval 15 15911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15911 : oddCount 15911 15 = 5 ∧ acceleratedOrbit 15 15911 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15911) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15911.1, data_15_15911.2]

/-- Complete interval computation for depth 15, residue 15912. -/
theorem bounds_15_15912 : exactInterval 15 15912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15912 : oddCount 15912 15 = 4 ∧ acceleratedOrbit 15 15912 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15912) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15912.1, data_15_15912.2]

/-- Complete interval computation for depth 15, residue 15913. -/
theorem bounds_15_15913 : exactInterval 15 15913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15913 : oddCount 15913 15 = 10 ∧ acceleratedOrbit 15 15913 = 28679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15913) = 3 ^ 10 * m + 28679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15913.1, data_15_15913.2]

/-- Complete interval computation for depth 15, residue 15914. -/
theorem bounds_15_15914 : exactInterval 15 15914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15914 : oddCount 15914 15 = 4 ∧ acceleratedOrbit 15 15914 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15914) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15914.1, data_15_15914.2]

/-- Complete interval computation for depth 15, residue 15915. -/
theorem bounds_15_15915 : exactInterval 15 15915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15915 : oddCount 15915 15 = 7 ∧ acceleratedOrbit 15 15915 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15915) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15915.1, data_15_15915.2]

/-- Complete interval computation for depth 15, residue 15916. -/
theorem bounds_15_15916 : exactInterval 15 15916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15916 : oddCount 15916 15 = 7 ∧ acceleratedOrbit 15 15916 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15916) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15916.1, data_15_15916.2]

/-- Complete interval computation for depth 15, residue 15917. -/
theorem bounds_15_15917 : exactInterval 15 15917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15917 : oddCount 15917 15 = 7 ∧ acceleratedOrbit 15 15917 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15917) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15917.1, data_15_15917.2]

/-- Complete interval computation for depth 15, residue 15918. -/
theorem bounds_15_15918 : exactInterval 15 15918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15918 : oddCount 15918 15 = 7 ∧ acceleratedOrbit 15 15918 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15918) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15918.1, data_15_15918.2]

/-- Complete interval computation for depth 15, residue 15919. -/
theorem bounds_15_15919 : exactInterval 15 15919 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15919) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15919 : oddCount 15919 15 = 9 ∧ acceleratedOrbit 15 15919 = 9563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15919) = 3 ^ 9 * m + 9563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15919.1, data_15_15919.2]

/-- Complete interval computation for depth 15, residue 15920. -/
theorem bounds_15_15920 : exactInterval 15 15920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15920 : oddCount 15920 15 = 4 ∧ acceleratedOrbit 15 15920 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15920) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15920.1, data_15_15920.2]

/-- Complete interval computation for depth 15, residue 15921. -/
theorem bounds_15_15921 : exactInterval 15 15921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15921 : oddCount 15921 15 = 9 ∧ acceleratedOrbit 15 15921 = 9568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15921) = 3 ^ 9 * m + 9568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15921.1, data_15_15921.2]

/-- Complete interval computation for depth 15, residue 15922. -/
theorem bounds_15_15922 : exactInterval 15 15922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15922 : oddCount 15922 15 = 9 ∧ acceleratedOrbit 15 15922 = 9568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15922) = 3 ^ 9 * m + 9568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15922.1, data_15_15922.2]

/-- Complete interval computation for depth 15, residue 15923. -/
theorem bounds_15_15923 : exactInterval 15 15923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15923 : oddCount 15923 15 = 9 ∧ acceleratedOrbit 15 15923 = 9568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15923) = 3 ^ 9 * m + 9568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15923.1, data_15_15923.2]

/-- Complete interval computation for depth 15, residue 15924. -/
theorem bounds_15_15924 : exactInterval 15 15924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15924 : oddCount 15924 15 = 4 ∧ acceleratedOrbit 15 15924 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15924) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15924.1, data_15_15924.2]

end Collatz.Research.PassageAtlas.Batch0486
