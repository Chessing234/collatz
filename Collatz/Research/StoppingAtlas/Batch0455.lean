import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0455

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3901. -/
theorem bounds_12_3901 : exactInterval 12 3901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3901 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3901) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3901 : oddCount 3901 12 = 6 ∧ acceleratedOrbit 12 3901 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3901 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3901) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3901.1, data_12_3901.2]

/-- Complete interval computation for depth 12, residue 3902. -/
theorem bounds_12_3902 : exactInterval 12 3902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3902 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3902) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3902 : oddCount 3902 12 = 8 ∧ acceleratedOrbit 12 3902 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3902 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3902) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3902.1, data_12_3902.2]

/-- Complete interval computation for depth 12, residue 3903. -/
theorem bounds_12_3903 : exactInterval 12 3903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3903 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3903) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3903 : oddCount 3903 12 = 8 ∧ acceleratedOrbit 12 3903 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3903 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3903) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3903.1, data_12_3903.2]

/-- Complete interval computation for depth 12, residue 3904. -/
theorem bounds_12_3904 : exactInterval 12 3904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3904 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3904) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3904 : oddCount 3904 12 = 4 ∧ acceleratedOrbit 12 3904 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3904 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3904) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3904.1, data_12_3904.2]

/-- Complete interval computation for depth 12, residue 3905. -/
theorem bounds_12_3905 : exactInterval 12 3905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3905 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3905) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3905 : oddCount 3905 12 = 5 ∧ acceleratedOrbit 12 3905 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3905 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3905) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3905.1, data_12_3905.2]

/-- Complete interval computation for depth 12, residue 3906. -/
theorem bounds_12_3906 : exactInterval 12 3906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3906 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3906) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3906 : oddCount 3906 12 = 5 ∧ acceleratedOrbit 12 3906 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3906 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3906) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3906.1, data_12_3906.2]

/-- Complete interval computation for depth 12, residue 3907. -/
theorem bounds_12_3907 : exactInterval 12 3907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3907 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3907) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3907 : oddCount 3907 12 = 5 ∧ acceleratedOrbit 12 3907 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3907 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3907) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3907.1, data_12_3907.2]

/-- Complete interval computation for depth 12, residue 3908. -/
theorem bounds_12_3908 : exactInterval 12 3908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3908 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3908) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3908 : oddCount 3908 12 = 5 ∧ acceleratedOrbit 12 3908 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3908 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3908) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3908.1, data_12_3908.2]

/-- Complete interval computation for depth 12, residue 3909. -/
theorem bounds_12_3909 : exactInterval 12 3909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3909 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3909) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3909 : oddCount 3909 12 = 5 ∧ acceleratedOrbit 12 3909 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3909 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3909) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3909.1, data_12_3909.2]

/-- Complete interval computation for depth 12, residue 3910. -/
theorem bounds_12_3910 : exactInterval 12 3910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3910 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3910) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3910 : oddCount 3910 12 = 5 ∧ acceleratedOrbit 12 3910 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3910 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3910) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3910.1, data_12_3910.2]

/-- Complete interval computation for depth 12, residue 3911. -/
theorem bounds_12_3911 : exactInterval 12 3911 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3911 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3911) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3911 : oddCount 3911 12 = 7 ∧ acceleratedOrbit 12 3911 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3911 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3911) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3911.1, data_12_3911.2]

/-- Complete interval computation for depth 12, residue 3912. -/
theorem bounds_12_3912 : exactInterval 12 3912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3912 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3912) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3912 : oddCount 3912 12 = 7 ∧ acceleratedOrbit 12 3912 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3912 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3912) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3912.1, data_12_3912.2]

/-- Complete interval computation for depth 12, residue 3913. -/
theorem bounds_12_3913 : exactInterval 12 3913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3913 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3913) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3913 : oddCount 3913 12 = 6 ∧ acceleratedOrbit 12 3913 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3913 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3913) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3913.1, data_12_3913.2]

/-- Complete interval computation for depth 12, residue 3914. -/
theorem bounds_12_3914 : exactInterval 12 3914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3914 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3914) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3914 : oddCount 3914 12 = 7 ∧ acceleratedOrbit 12 3914 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3914 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3914) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3914.1, data_12_3914.2]

/-- Complete interval computation for depth 12, residue 3915. -/
theorem bounds_12_3915 : exactInterval 12 3915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3915 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3915) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3915 : oddCount 3915 12 = 5 ∧ acceleratedOrbit 12 3915 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3915 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3915) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3915.1, data_12_3915.2]

end Collatz.Research.StoppingAtlas.Batch0455
