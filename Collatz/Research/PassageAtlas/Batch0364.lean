import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0364

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11894. -/
theorem bounds_15_11894 : exactInterval 15 11894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11894 : oddCount 11894 15 = 6 ∧ acceleratedOrbit 15 11894 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11894) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11894.1, data_15_11894.2]

/-- Complete interval computation for depth 15, residue 11895. -/
theorem bounds_15_11895 : exactInterval 15 11895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11895 : oddCount 11895 15 = 6 ∧ acceleratedOrbit 15 11895 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11895) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11895.1, data_15_11895.2]

/-- Complete interval computation for depth 15, residue 11896. -/
theorem bounds_15_11896 : exactInterval 15 11896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11896 : oddCount 11896 15 = 9 ∧ acceleratedOrbit 15 11896 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11896) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11896.1, data_15_11896.2]

/-- Complete interval computation for depth 15, residue 11897. -/
theorem bounds_15_11897 : exactInterval 15 11897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11897 : oddCount 11897 15 = 9 ∧ acceleratedOrbit 15 11897 = 7148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11897) = 3 ^ 9 * m + 7148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11897.1, data_15_11897.2]

/-- Complete interval computation for depth 15, residue 11898. -/
theorem bounds_15_11898 : exactInterval 15 11898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11898 : oddCount 11898 15 = 9 ∧ acceleratedOrbit 15 11898 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11898) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11898.1, data_15_11898.2]

/-- Complete interval computation for depth 15, residue 11899. -/
theorem bounds_15_11899 : exactInterval 15 11899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11899 : oddCount 11899 15 = 6 ∧ acceleratedOrbit 15 11899 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11899) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11899.1, data_15_11899.2]

/-- Complete interval computation for depth 15, residue 11900. -/
theorem bounds_15_11900 : exactInterval 15 11900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11900 : oddCount 11900 15 = 8 ∧ acceleratedOrbit 15 11900 = 2384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11900) = 3 ^ 8 * m + 2384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11900.1, data_15_11900.2]

/-- Complete interval computation for depth 15, residue 11901. -/
theorem bounds_15_11901 : exactInterval 15 11901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11901 : oddCount 11901 15 = 8 ∧ acceleratedOrbit 15 11901 = 2384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11901) = 3 ^ 8 * m + 2384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11901.1, data_15_11901.2]

/-- Complete interval computation for depth 15, residue 11902. -/
theorem bounds_15_11902 : exactInterval 15 11902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11902 : oddCount 11902 15 = 8 ∧ acceleratedOrbit 15 11902 = 2384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11902) = 3 ^ 8 * m + 2384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11902.1, data_15_11902.2]

/-- Complete interval computation for depth 15, residue 11903. -/
theorem bounds_15_11903 : exactInterval 15 11903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11903 : oddCount 11903 15 = 13 ∧ acceleratedOrbit 15 11903 = 579190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11903) = 3 ^ 13 * m + 579190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11903.1, data_15_11903.2]

/-- Complete interval computation for depth 15, residue 11904. -/
theorem bounds_15_11904 : exactInterval 15 11904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11904 : oddCount 11904 15 = 3 ∧ acceleratedOrbit 15 11904 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11904) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11904.1, data_15_11904.2]

/-- Complete interval computation for depth 15, residue 11905. -/
theorem bounds_15_11905 : exactInterval 15 11905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11905 : oddCount 11905 15 = 10 ∧ acceleratedOrbit 15 11905 = 21460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11905) = 3 ^ 10 * m + 21460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11905.1, data_15_11905.2]

/-- Complete interval computation for depth 15, residue 11906. -/
theorem bounds_15_11906 : exactInterval 15 11906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11906 : oddCount 11906 15 = 5 ∧ acceleratedOrbit 15 11906 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11906) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11906.1, data_15_11906.2]

/-- Complete interval computation for depth 15, residue 11907. -/
theorem bounds_15_11907 : exactInterval 15 11907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11907 : oddCount 11907 15 = 5 ∧ acceleratedOrbit 15 11907 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11907) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11907.1, data_15_11907.2]

/-- Complete interval computation for depth 15, residue 11908. -/
theorem bounds_15_11908 : exactInterval 15 11908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11908 : oddCount 11908 15 = 7 ∧ acceleratedOrbit 15 11908 = 796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11908) = 3 ^ 7 * m + 796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11908.1, data_15_11908.2]

/-- Complete interval computation for depth 15, residue 11909. -/
theorem bounds_15_11909 : exactInterval 15 11909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11909 : oddCount 11909 15 = 7 ∧ acceleratedOrbit 15 11909 = 796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11909) = 3 ^ 7 * m + 796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11909.1, data_15_11909.2]

/-- Complete interval computation for depth 15, residue 11910. -/
theorem bounds_15_11910 : exactInterval 15 11910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11910 : oddCount 11910 15 = 7 ∧ acceleratedOrbit 15 11910 = 796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11910) = 3 ^ 7 * m + 796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11910.1, data_15_11910.2]

/-- Complete interval computation for depth 15, residue 11911. -/
theorem bounds_15_11911 : exactInterval 15 11911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11911 : oddCount 11911 15 = 8 ∧ acceleratedOrbit 15 11911 = 2386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11911) = 3 ^ 8 * m + 2386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11911.1, data_15_11911.2]

/-- Complete interval computation for depth 15, residue 11912. -/
theorem bounds_15_11912 : exactInterval 15 11912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11912 : oddCount 11912 15 = 5 ∧ acceleratedOrbit 15 11912 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11912) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11912.1, data_15_11912.2]

/-- Complete interval computation for depth 15, residue 11913. -/
theorem bounds_15_11913 : exactInterval 15 11913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11913 : oddCount 11913 15 = 11 ∧ acceleratedOrbit 15 11913 = 64415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11913) = 3 ^ 11 * m + 64415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11913.1, data_15_11913.2]

/-- Complete interval computation for depth 15, residue 11914. -/
theorem bounds_15_11914 : exactInterval 15 11914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11914 : oddCount 11914 15 = 5 ∧ acceleratedOrbit 15 11914 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11914) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11914.1, data_15_11914.2]

/-- Complete interval computation for depth 15, residue 11915. -/
theorem bounds_15_11915 : exactInterval 15 11915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11915 : oddCount 11915 15 = 7 ∧ acceleratedOrbit 15 11915 = 796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11915) = 3 ^ 7 * m + 796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11915.1, data_15_11915.2]

/-- Complete interval computation for depth 15, residue 11916. -/
theorem bounds_15_11916 : exactInterval 15 11916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11916 : oddCount 11916 15 = 5 ∧ acceleratedOrbit 15 11916 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11916) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11916.1, data_15_11916.2]

/-- Complete interval computation for depth 15, residue 11917. -/
theorem bounds_15_11917 : exactInterval 15 11917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11917 : oddCount 11917 15 = 5 ∧ acceleratedOrbit 15 11917 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11917) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11917.1, data_15_11917.2]

/-- Complete interval computation for depth 15, residue 11918. -/
theorem bounds_15_11918 : exactInterval 15 11918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11918 : oddCount 11918 15 = 8 ∧ acceleratedOrbit 15 11918 = 2387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11918) = 3 ^ 8 * m + 2387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11918.1, data_15_11918.2]

/-- Complete interval computation for depth 15, residue 11919. -/
theorem bounds_15_11919 : exactInterval 15 11919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11919 : oddCount 11919 15 = 8 ∧ acceleratedOrbit 15 11919 = 2387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11919) = 3 ^ 8 * m + 2387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11919.1, data_15_11919.2]

/-- Complete interval computation for depth 15, residue 11920. -/
theorem bounds_15_11920 : exactInterval 15 11920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11920 : oddCount 11920 15 = 8 ∧ acceleratedOrbit 15 11920 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11920) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11920.1, data_15_11920.2]

/-- Complete interval computation for depth 15, residue 11921. -/
theorem bounds_15_11921 : exactInterval 15 11921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11921 : oddCount 11921 15 = 8 ∧ acceleratedOrbit 15 11921 = 2389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11921) = 3 ^ 8 * m + 2389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11921.1, data_15_11921.2]

/-- Complete interval computation for depth 15, residue 11922. -/
theorem bounds_15_11922 : exactInterval 15 11922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11922 : oddCount 11922 15 = 8 ∧ acceleratedOrbit 15 11922 = 2389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11922) = 3 ^ 8 * m + 2389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11922.1, data_15_11922.2]

/-- Complete interval computation for depth 15, residue 11923. -/
theorem bounds_15_11923 : exactInterval 15 11923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11923 : oddCount 11923 15 = 8 ∧ acceleratedOrbit 15 11923 = 2389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11923) = 3 ^ 8 * m + 2389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11923.1, data_15_11923.2]

/-- Complete interval computation for depth 15, residue 11924. -/
theorem bounds_15_11924 : exactInterval 15 11924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11924 : oddCount 11924 15 = 8 ∧ acceleratedOrbit 15 11924 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11924) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11924.1, data_15_11924.2]

/-- Complete interval computation for depth 15, residue 11925. -/
theorem bounds_15_11925 : exactInterval 15 11925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11925 : oddCount 11925 15 = 8 ∧ acceleratedOrbit 15 11925 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11925) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11925.1, data_15_11925.2]

/-- Complete interval computation for depth 15, residue 11926. -/
theorem bounds_15_11926 : exactInterval 15 11926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11926 : oddCount 11926 15 = 5 ∧ acceleratedOrbit 15 11926 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11926) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11926.1, data_15_11926.2]

end Collatz.Research.PassageAtlas.Batch0364
