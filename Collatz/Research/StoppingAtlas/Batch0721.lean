import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0721

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3891. -/
theorem bounds_13_3891 : exactInterval 13 3891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3891 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3891) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3891 : oddCount 3891 13 = 5 ∧ acceleratedOrbit 13 3891 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3891 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3891) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3891.1, data_13_3891.2]

/-- Complete interval computation for depth 13, residue 3892. -/
theorem bounds_13_3892 : exactInterval 13 3892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3892 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3892) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3892 : oddCount 3892 13 = 6 ∧ acceleratedOrbit 13 3892 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3892 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3892) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3892.1, data_13_3892.2]

/-- Complete interval computation for depth 13, residue 3893. -/
theorem bounds_13_3893 : exactInterval 13 3893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3893 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3893) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3893 : oddCount 3893 13 = 6 ∧ acceleratedOrbit 13 3893 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3893 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3893) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3893.1, data_13_3893.2]

/-- Complete interval computation for depth 13, residue 3894. -/
theorem bounds_13_3894 : exactInterval 13 3894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3894 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3894) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3894 : oddCount 3894 13 = 8 ∧ acceleratedOrbit 13 3894 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3894 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3894) = 3 ^ 8 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3894.1, data_13_3894.2]

/-- Complete interval computation for depth 13, residue 3895. -/
theorem bounds_13_3895 : exactInterval 13 3895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3895 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3895) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3895 : oddCount 3895 13 = 8 ∧ acceleratedOrbit 13 3895 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3895 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3895) = 3 ^ 8 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3895.1, data_13_3895.2]

/-- Complete interval computation for depth 13, residue 3896. -/
theorem bounds_13_3896 : exactInterval 13 3896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3896 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3896) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3896 : oddCount 3896 13 = 7 ∧ acceleratedOrbit 13 3896 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3896 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3896) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3896.1, data_13_3896.2]

/-- Complete interval computation for depth 13, residue 3897. -/
theorem bounds_13_3897 : exactInterval 13 3897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3897 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3897) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3897 : oddCount 3897 13 = 6 ∧ acceleratedOrbit 13 3897 = 347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3897 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3897) = 3 ^ 6 * m + 347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3897.1, data_13_3897.2]

/-- Complete interval computation for depth 13, residue 3898. -/
theorem bounds_13_3898 : exactInterval 13 3898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3898 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3898) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3898 : oddCount 3898 13 = 7 ∧ acceleratedOrbit 13 3898 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3898 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3898) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3898.1, data_13_3898.2]

/-- Complete interval computation for depth 13, residue 3899. -/
theorem bounds_13_3899 : exactInterval 13 3899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3899 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3899) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3899 : oddCount 3899 13 = 7 ∧ acceleratedOrbit 13 3899 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3899 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3899) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3899.1, data_13_3899.2]

/-- Complete interval computation for depth 13, residue 3900. -/
theorem bounds_13_3900 : exactInterval 13 3900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3900 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3900) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3900 : oddCount 3900 13 = 7 ∧ acceleratedOrbit 13 3900 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3900 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3900) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3900.1, data_13_3900.2]

/-- Complete interval computation for depth 13, residue 3901. -/
theorem bounds_13_3901 : exactInterval 13 3901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3901 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3901) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3901 : oddCount 3901 13 = 7 ∧ acceleratedOrbit 13 3901 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3901 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3901) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3901.1, data_13_3901.2]

/-- Complete interval computation for depth 13, residue 3902. -/
theorem bounds_13_3902 : exactInterval 13 3902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3902 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3902) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3902 : oddCount 3902 13 = 8 ∧ acceleratedOrbit 13 3902 = 3127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3902 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3902) = 3 ^ 8 * m + 3127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3902.1, data_13_3902.2]

/-- Complete interval computation for depth 13, residue 3903. -/
theorem bounds_13_3903 : exactInterval 13 3903 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3903 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3903) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3903 : oddCount 3903 13 = 8 ∧ acceleratedOrbit 13 3903 = 3127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3903 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3903) = 3 ^ 8 * m + 3127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3903.1, data_13_3903.2]

/-- Complete interval computation for depth 13, residue 3904. -/
theorem bounds_13_3904 : exactInterval 13 3904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3904 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3904) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3904 : oddCount 3904 13 = 4 ∧ acceleratedOrbit 13 3904 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3904 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3904) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3904.1, data_13_3904.2]

/-- Complete interval computation for depth 13, residue 3905. -/
theorem bounds_13_3905 : exactInterval 13 3905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3905 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3905) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3905 : oddCount 3905 13 = 6 ∧ acceleratedOrbit 13 3905 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3905 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3905) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3905.1, data_13_3905.2]

end Collatz.Research.StoppingAtlas.Batch0721
