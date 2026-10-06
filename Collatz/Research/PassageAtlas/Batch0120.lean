import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0120

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3899. -/
theorem bounds_15_3899 : exactInterval 15 3899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3899 : oddCount 3899 15 = 9 ∧ acceleratedOrbit 15 3899 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3899) = 3 ^ 9 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3899.1, data_15_3899.2]

/-- Complete interval computation for depth 15, residue 3900. -/
theorem bounds_15_3900 : exactInterval 15 3900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3900 : oddCount 3900 15 = 9 ∧ acceleratedOrbit 15 3900 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3900) = 3 ^ 9 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3900.1, data_15_3900.2]

/-- Complete interval computation for depth 15, residue 3901. -/
theorem bounds_15_3901 : exactInterval 15 3901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3901 : oddCount 3901 15 = 9 ∧ acceleratedOrbit 15 3901 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3901) = 3 ^ 9 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3901.1, data_15_3901.2]

/-- Complete interval computation for depth 15, residue 3902. -/
theorem bounds_15_3902 : exactInterval 15 3902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3902 : oddCount 3902 15 = 10 ∧ acceleratedOrbit 15 3902 = 7037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3902) = 3 ^ 10 * m + 7037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3902.1, data_15_3902.2]

/-- Complete interval computation for depth 15, residue 3903. -/
theorem bounds_15_3903 : exactInterval 15 3903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3903 : oddCount 3903 15 = 10 ∧ acceleratedOrbit 15 3903 = 7037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3903) = 3 ^ 10 * m + 7037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3903.1, data_15_3903.2]

/-- Complete interval computation for depth 15, residue 3904. -/
theorem bounds_15_3904 : exactInterval 15 3904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3904 : oddCount 3904 15 = 4 ∧ acceleratedOrbit 15 3904 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3904) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3904.1, data_15_3904.2]

/-- Complete interval computation for depth 15, residue 3905. -/
theorem bounds_15_3905 : exactInterval 15 3905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3905 : oddCount 3905 15 = 7 ∧ acceleratedOrbit 15 3905 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3905) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3905.1, data_15_3905.2]

/-- Complete interval computation for depth 15, residue 3906. -/
theorem bounds_15_3906 : exactInterval 15 3906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3906 : oddCount 3906 15 = 5 ∧ acceleratedOrbit 15 3906 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3906) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3906.1, data_15_3906.2]

/-- Complete interval computation for depth 15, residue 3907. -/
theorem bounds_15_3907 : exactInterval 15 3907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3907 : oddCount 3907 15 = 5 ∧ acceleratedOrbit 15 3907 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3907) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3907.1, data_15_3907.2]

/-- Complete interval computation for depth 15, residue 3908. -/
theorem bounds_15_3908 : exactInterval 15 3908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3908 : oddCount 3908 15 = 7 ∧ acceleratedOrbit 15 3908 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3908) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3908.1, data_15_3908.2]

/-- Complete interval computation for depth 15, residue 3909. -/
theorem bounds_15_3909 : exactInterval 15 3909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3909 : oddCount 3909 15 = 7 ∧ acceleratedOrbit 15 3909 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3909) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3909.1, data_15_3909.2]

/-- Complete interval computation for depth 15, residue 3910. -/
theorem bounds_15_3910 : exactInterval 15 3910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3910 : oddCount 3910 15 = 7 ∧ acceleratedOrbit 15 3910 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3910) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3910.1, data_15_3910.2]

/-- Complete interval computation for depth 15, residue 3911. -/
theorem bounds_15_3911 : exactInterval 15 3911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3911 : oddCount 3911 15 = 9 ∧ acceleratedOrbit 15 3911 = 2351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3911) = 3 ^ 9 * m + 2351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3911.1, data_15_3911.2]

/-- Complete interval computation for depth 15, residue 3912. -/
theorem bounds_15_3912 : exactInterval 15 3912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3912 : oddCount 3912 15 = 7 ∧ acceleratedOrbit 15 3912 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3912) = 3 ^ 7 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3912.1, data_15_3912.2]

/-- Complete interval computation for depth 15, residue 3913. -/
theorem bounds_15_3913 : exactInterval 15 3913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3913 : oddCount 3913 15 = 8 ∧ acceleratedOrbit 15 3913 = 785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3913) = 3 ^ 8 * m + 785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3913.1, data_15_3913.2]

/-- Complete interval computation for depth 15, residue 3914. -/
theorem bounds_15_3914 : exactInterval 15 3914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3914 : oddCount 3914 15 = 7 ∧ acceleratedOrbit 15 3914 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3914) = 3 ^ 7 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3914.1, data_15_3914.2]

/-- Complete interval computation for depth 15, residue 3915. -/
theorem bounds_15_3915 : exactInterval 15 3915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3915 : oddCount 3915 15 = 7 ∧ acceleratedOrbit 15 3915 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3915) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3915.1, data_15_3915.2]

/-- Complete interval computation for depth 15, residue 3916. -/
theorem bounds_15_3916 : exactInterval 15 3916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3916 : oddCount 3916 15 = 7 ∧ acceleratedOrbit 15 3916 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3916) = 3 ^ 7 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3916.1, data_15_3916.2]

/-- Complete interval computation for depth 15, residue 3917. -/
theorem bounds_15_3917 : exactInterval 15 3917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3917 : oddCount 3917 15 = 7 ∧ acceleratedOrbit 15 3917 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3917) = 3 ^ 7 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3917.1, data_15_3917.2]

/-- Complete interval computation for depth 15, residue 3918. -/
theorem bounds_15_3918 : exactInterval 15 3918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3918 : oddCount 3918 15 = 10 ∧ acceleratedOrbit 15 3918 = 7067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3918) = 3 ^ 10 * m + 7067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3918.1, data_15_3918.2]

/-- Complete interval computation for depth 15, residue 3919. -/
theorem bounds_15_3919 : exactInterval 15 3919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3919 : oddCount 3919 15 = 10 ∧ acceleratedOrbit 15 3919 = 7067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3919) = 3 ^ 10 * m + 7067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3919.1, data_15_3919.2]

/-- Complete interval computation for depth 15, residue 3920. -/
theorem bounds_15_3920 : exactInterval 15 3920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3920 : oddCount 3920 15 = 4 ∧ acceleratedOrbit 15 3920 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3920) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3920.1, data_15_3920.2]

/-- Complete interval computation for depth 15, residue 3921. -/
theorem bounds_15_3921 : exactInterval 15 3921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3921 : oddCount 3921 15 = 7 ∧ acceleratedOrbit 15 3921 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3921) = 3 ^ 7 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3921.1, data_15_3921.2]

/-- Complete interval computation for depth 15, residue 3922. -/
theorem bounds_15_3922 : exactInterval 15 3922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3922 : oddCount 3922 15 = 12 ∧ acceleratedOrbit 15 3922 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3922) = 3 ^ 12 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3922.1, data_15_3922.2]

/-- Complete interval computation for depth 15, residue 3923. -/
theorem bounds_15_3923 : exactInterval 15 3923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3923 : oddCount 3923 15 = 12 ∧ acceleratedOrbit 15 3923 = 63665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3923) = 3 ^ 12 * m + 63665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3923.1, data_15_3923.2]

/-- Complete interval computation for depth 15, residue 3924. -/
theorem bounds_15_3924 : exactInterval 15 3924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3924 : oddCount 3924 15 = 4 ∧ acceleratedOrbit 15 3924 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3924) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3924.1, data_15_3924.2]

/-- Complete interval computation for depth 15, residue 3925. -/
theorem bounds_15_3925 : exactInterval 15 3925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3925 : oddCount 3925 15 = 4 ∧ acceleratedOrbit 15 3925 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3925) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3925.1, data_15_3925.2]

/-- Complete interval computation for depth 15, residue 3926. -/
theorem bounds_15_3926 : exactInterval 15 3926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3926 : oddCount 3926 15 = 9 ∧ acceleratedOrbit 15 3926 = 2362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3926) = 3 ^ 9 * m + 2362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3926.1, data_15_3926.2]

/-- Complete interval computation for depth 15, residue 3927. -/
theorem bounds_15_3927 : exactInterval 15 3927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3927 : oddCount 3927 15 = 9 ∧ acceleratedOrbit 15 3927 = 2362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3927) = 3 ^ 9 * m + 2362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3927.1, data_15_3927.2]

/-- Complete interval computation for depth 15, residue 3928. -/
theorem bounds_15_3928 : exactInterval 15 3928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3928 : oddCount 3928 15 = 9 ∧ acceleratedOrbit 15 3928 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3928) = 3 ^ 9 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3928.1, data_15_3928.2]

/-- Complete interval computation for depth 15, residue 3929. -/
theorem bounds_15_3929 : exactInterval 15 3929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3929 : oddCount 3929 15 = 7 ∧ acceleratedOrbit 15 3929 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3929) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3929.1, data_15_3929.2]

/-- Complete interval computation for depth 15, residue 3930. -/
theorem bounds_15_3930 : exactInterval 15 3930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3930 : oddCount 3930 15 = 9 ∧ acceleratedOrbit 15 3930 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3930) = 3 ^ 9 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3930.1, data_15_3930.2]

/-- Complete interval computation for depth 15, residue 3931. -/
theorem bounds_15_3931 : exactInterval 15 3931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3931 : oddCount 3931 15 = 11 ∧ acceleratedOrbit 15 3931 = 21262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3931) = 3 ^ 11 * m + 21262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3931.1, data_15_3931.2]

end Collatz.Research.PassageAtlas.Batch0120
