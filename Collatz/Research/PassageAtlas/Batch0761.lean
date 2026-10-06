import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0761

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24903. -/
theorem bounds_15_24903 : exactInterval 15 24903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24903 : oddCount 24903 15 = 10 ∧ acceleratedOrbit 15 24903 = 44879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24903) = 3 ^ 10 * m + 44879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24903.1, data_15_24903.2]

/-- Complete interval computation for depth 15, residue 24904. -/
theorem bounds_15_24904 : exactInterval 15 24904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24904 : oddCount 24904 15 = 7 ∧ acceleratedOrbit 15 24904 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24904) = 3 ^ 7 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24904.1, data_15_24904.2]

/-- Complete interval computation for depth 15, residue 24905. -/
theorem bounds_15_24905 : exactInterval 15 24905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24905 : oddCount 24905 15 = 8 ∧ acceleratedOrbit 15 24905 = 4988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24905) = 3 ^ 8 * m + 4988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24905.1, data_15_24905.2]

/-- Complete interval computation for depth 15, residue 24906. -/
theorem bounds_15_24906 : exactInterval 15 24906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24906 : oddCount 24906 15 = 7 ∧ acceleratedOrbit 15 24906 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24906) = 3 ^ 7 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24906.1, data_15_24906.2]

/-- Complete interval computation for depth 15, residue 24907. -/
theorem bounds_15_24907 : exactInterval 15 24907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24907 : oddCount 24907 15 = 7 ∧ acceleratedOrbit 15 24907 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24907) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24907.1, data_15_24907.2]

/-- Complete interval computation for depth 15, residue 24908. -/
theorem bounds_15_24908 : exactInterval 15 24908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24908 : oddCount 24908 15 = 7 ∧ acceleratedOrbit 15 24908 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24908) = 3 ^ 7 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24908.1, data_15_24908.2]

/-- Complete interval computation for depth 15, residue 24909. -/
theorem bounds_15_24909 : exactInterval 15 24909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24909 : oddCount 24909 15 = 7 ∧ acceleratedOrbit 15 24909 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24909) = 3 ^ 7 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24909.1, data_15_24909.2]

/-- Complete interval computation for depth 15, residue 24910. -/
theorem bounds_15_24910 : exactInterval 15 24910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24910 : oddCount 24910 15 = 10 ∧ acceleratedOrbit 15 24910 = 44894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24910) = 3 ^ 10 * m + 44894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24910.1, data_15_24910.2]

/-- Complete interval computation for depth 15, residue 24911. -/
theorem bounds_15_24911 : exactInterval 15 24911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24911 : oddCount 24911 15 = 10 ∧ acceleratedOrbit 15 24911 = 44894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24911) = 3 ^ 10 * m + 44894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24911.1, data_15_24911.2]

/-- Complete interval computation for depth 15, residue 24912. -/
theorem bounds_15_24912 : exactInterval 15 24912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24912 : oddCount 24912 15 = 5 ∧ acceleratedOrbit 15 24912 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24912) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24912.1, data_15_24912.2]

/-- Complete interval computation for depth 15, residue 24913. -/
theorem bounds_15_24913 : exactInterval 15 24913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24913 : oddCount 24913 15 = 7 ∧ acceleratedOrbit 15 24913 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24913) = 3 ^ 7 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24913.1, data_15_24913.2]

/-- Complete interval computation for depth 15, residue 24914. -/
theorem bounds_15_24914 : exactInterval 15 24914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24914 : oddCount 24914 15 = 10 ∧ acceleratedOrbit 15 24914 = 44902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24914) = 3 ^ 10 * m + 44902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24914.1, data_15_24914.2]

/-- Complete interval computation for depth 15, residue 24915. -/
theorem bounds_15_24915 : exactInterval 15 24915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24915 : oddCount 24915 15 = 10 ∧ acceleratedOrbit 15 24915 = 44902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24915) = 3 ^ 10 * m + 44902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24915.1, data_15_24915.2]

/-- Complete interval computation for depth 15, residue 24916. -/
theorem bounds_15_24916 : exactInterval 15 24916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24916 : oddCount 24916 15 = 5 ∧ acceleratedOrbit 15 24916 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24916) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24916.1, data_15_24916.2]

/-- Complete interval computation for depth 15, residue 24917. -/
theorem bounds_15_24917 : exactInterval 15 24917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24917 : oddCount 24917 15 = 5 ∧ acceleratedOrbit 15 24917 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24917) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24917.1, data_15_24917.2]

/-- Complete interval computation for depth 15, residue 24918. -/
theorem bounds_15_24918 : exactInterval 15 24918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24918 : oddCount 24918 15 = 7 ∧ acceleratedOrbit 15 24918 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24918) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24918.1, data_15_24918.2]

/-- Complete interval computation for depth 15, residue 24919. -/
theorem bounds_15_24919 : exactInterval 15 24919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24919 : oddCount 24919 15 = 7 ∧ acceleratedOrbit 15 24919 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24919) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24919.1, data_15_24919.2]

/-- Complete interval computation for depth 15, residue 24920. -/
theorem bounds_15_24920 : exactInterval 15 24920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24920 : oddCount 24920 15 = 5 ∧ acceleratedOrbit 15 24920 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24920) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24920.1, data_15_24920.2]

/-- Complete interval computation for depth 15, residue 24921. -/
theorem bounds_15_24921 : exactInterval 15 24921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24921 : oddCount 24921 15 = 9 ∧ acceleratedOrbit 15 24921 = 14975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24921) = 3 ^ 9 * m + 14975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24921.1, data_15_24921.2]

/-- Complete interval computation for depth 15, residue 24922. -/
theorem bounds_15_24922 : exactInterval 15 24922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24922 : oddCount 24922 15 = 5 ∧ acceleratedOrbit 15 24922 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24922) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24922.1, data_15_24922.2]

/-- Complete interval computation for depth 15, residue 24923. -/
theorem bounds_15_24923 : exactInterval 15 24923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24923 : oddCount 24923 15 = 7 ∧ acceleratedOrbit 15 24923 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24923) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24923.1, data_15_24923.2]

/-- Complete interval computation for depth 15, residue 24924. -/
theorem bounds_15_24924 : exactInterval 15 24924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24924 : oddCount 24924 15 = 5 ∧ acceleratedOrbit 15 24924 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24924) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24924.1, data_15_24924.2]

/-- Complete interval computation for depth 15, residue 24925. -/
theorem bounds_15_24925 : exactInterval 15 24925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24925 : oddCount 24925 15 = 5 ∧ acceleratedOrbit 15 24925 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24925) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24925.1, data_15_24925.2]

/-- Complete interval computation for depth 15, residue 24926. -/
theorem bounds_15_24926 : exactInterval 15 24926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24926 : oddCount 24926 15 = 9 ∧ acceleratedOrbit 15 24926 = 14975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24926) = 3 ^ 9 * m + 14975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24926.1, data_15_24926.2]

/-- Complete interval computation for depth 15, residue 24927. -/
theorem bounds_15_24927 : exactInterval 15 24927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24927 : oddCount 24927 15 = 9 ∧ acceleratedOrbit 15 24927 = 14975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24927) = 3 ^ 9 * m + 14975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24927.1, data_15_24927.2]

/-- Complete interval computation for depth 15, residue 24928. -/
theorem bounds_15_24928 : exactInterval 15 24928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24928 : oddCount 24928 15 = 6 ∧ acceleratedOrbit 15 24928 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24928) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24928.1, data_15_24928.2]

/-- Complete interval computation for depth 15, residue 24929. -/
theorem bounds_15_24929 : exactInterval 15 24929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24929 : oddCount 24929 15 = 7 ∧ acceleratedOrbit 15 24929 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24929) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24929.1, data_15_24929.2]

/-- Complete interval computation for depth 15, residue 24930. -/
theorem bounds_15_24930 : exactInterval 15 24930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24930 : oddCount 24930 15 = 5 ∧ acceleratedOrbit 15 24930 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24930) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24930.1, data_15_24930.2]

/-- Complete interval computation for depth 15, residue 24931. -/
theorem bounds_15_24931 : exactInterval 15 24931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24931 : oddCount 24931 15 = 5 ∧ acceleratedOrbit 15 24931 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24931) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24931.1, data_15_24931.2]

/-- Complete interval computation for depth 15, residue 24932. -/
theorem bounds_15_24932 : exactInterval 15 24932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24932 : oddCount 24932 15 = 5 ∧ acceleratedOrbit 15 24932 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24932) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24932.1, data_15_24932.2]

/-- Complete interval computation for depth 15, residue 24933. -/
theorem bounds_15_24933 : exactInterval 15 24933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24933 : oddCount 24933 15 = 5 ∧ acceleratedOrbit 15 24933 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24933) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24933.1, data_15_24933.2]

/-- Complete interval computation for depth 15, residue 24934. -/
theorem bounds_15_24934 : exactInterval 15 24934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24934 : oddCount 24934 15 = 5 ∧ acceleratedOrbit 15 24934 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24934) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24934.1, data_15_24934.2]

/-- Complete interval computation for depth 15, residue 24935. -/
theorem bounds_15_24935 : exactInterval 15 24935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24935 : oddCount 24935 15 = 11 ∧ acceleratedOrbit 15 24935 = 134810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24935) = 3 ^ 11 * m + 134810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24935.1, data_15_24935.2]

end Collatz.Research.PassageAtlas.Batch0761
