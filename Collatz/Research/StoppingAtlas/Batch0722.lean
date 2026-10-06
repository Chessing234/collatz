import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0722

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3906. -/
theorem bounds_13_3906 : exactInterval 13 3906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3906 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3906) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3906 : oddCount 3906 13 = 5 ∧ acceleratedOrbit 13 3906 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3906 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3906) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3906.1, data_13_3906.2]

/-- Complete interval computation for depth 13, residue 3907. -/
theorem bounds_13_3907 : exactInterval 13 3907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3907 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3907) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3907 : oddCount 3907 13 = 5 ∧ acceleratedOrbit 13 3907 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3907 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3907) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3907.1, data_13_3907.2]

/-- Complete interval computation for depth 13, residue 3908. -/
theorem bounds_13_3908 : exactInterval 13 3908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3908 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3908) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3908 : oddCount 3908 13 = 6 ∧ acceleratedOrbit 13 3908 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3908 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3908) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3908.1, data_13_3908.2]

/-- Complete interval computation for depth 13, residue 3909. -/
theorem bounds_13_3909 : exactInterval 13 3909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3909 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3909) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3909 : oddCount 3909 13 = 6 ∧ acceleratedOrbit 13 3909 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3909 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3909) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3909.1, data_13_3909.2]

/-- Complete interval computation for depth 13, residue 3910. -/
theorem bounds_13_3910 : exactInterval 13 3910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3910 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3910) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3910 : oddCount 3910 13 = 6 ∧ acceleratedOrbit 13 3910 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3910 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3910) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3910.1, data_13_3910.2]

/-- Complete interval computation for depth 13, residue 3911. -/
theorem bounds_13_3911 : exactInterval 13 3911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3911 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3911) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3911 : oddCount 3911 13 = 8 ∧ acceleratedOrbit 13 3911 = 3134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3911 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3911) = 3 ^ 8 * m + 3134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3911.1, data_13_3911.2]

/-- Complete interval computation for depth 13, residue 3912. -/
theorem bounds_13_3912 : exactInterval 13 3912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3912 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3912) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3912 : oddCount 3912 13 = 7 ∧ acceleratedOrbit 13 3912 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3912 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3912) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3912.1, data_13_3912.2]

/-- Complete interval computation for depth 13, residue 3913. -/
theorem bounds_13_3913 : exactInterval 13 3913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3913 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3913) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3913 : oddCount 3913 13 = 7 ∧ acceleratedOrbit 13 3913 = 1046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3913 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3913) = 3 ^ 7 * m + 1046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3913.1, data_13_3913.2]

/-- Complete interval computation for depth 13, residue 3914. -/
theorem bounds_13_3914 : exactInterval 13 3914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3914 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3914) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3914 : oddCount 3914 13 = 7 ∧ acceleratedOrbit 13 3914 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3914 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3914) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3914.1, data_13_3914.2]

/-- Complete interval computation for depth 13, residue 3915. -/
theorem bounds_13_3915 : exactInterval 13 3915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3915 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3915) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3915 : oddCount 3915 13 = 6 ∧ acceleratedOrbit 13 3915 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3915 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3915) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3915.1, data_13_3915.2]

/-- Complete interval computation for depth 13, residue 3916. -/
theorem bounds_13_3916 : exactInterval 13 3916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3916 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3916) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3916 : oddCount 3916 13 = 7 ∧ acceleratedOrbit 13 3916 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3916 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3916) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3916.1, data_13_3916.2]

/-- Complete interval computation for depth 13, residue 3917. -/
theorem bounds_13_3917 : exactInterval 13 3917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3917 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3917) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3917 : oddCount 3917 13 = 7 ∧ acceleratedOrbit 13 3917 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3917 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3917) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3917.1, data_13_3917.2]

/-- Complete interval computation for depth 13, residue 3918. -/
theorem bounds_13_3918 : exactInterval 13 3918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3918 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3918) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3918 : oddCount 3918 13 = 9 ∧ acceleratedOrbit 13 3918 = 9422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3918 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3918) = 3 ^ 9 * m + 9422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3918.1, data_13_3918.2]

/-- Complete interval computation for depth 13, residue 3919. -/
theorem bounds_13_3919 : exactInterval 13 3919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3919 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3919) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3919 : oddCount 3919 13 = 9 ∧ acceleratedOrbit 13 3919 = 9422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3919 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3919) = 3 ^ 9 * m + 9422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3919.1, data_13_3919.2]

/-- Complete interval computation for depth 13, residue 3920. -/
theorem bounds_13_3920 : exactInterval 13 3920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3920 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3920) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3920 : oddCount 3920 13 = 4 ∧ acceleratedOrbit 13 3920 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3920 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3920) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3920.1, data_13_3920.2]

end Collatz.Research.StoppingAtlas.Batch0722
