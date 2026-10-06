import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0454

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3886. -/
theorem bounds_12_3886 : exactInterval 12 3886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3886 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3886) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3886 : oddCount 3886 12 = 4 ∧ acceleratedOrbit 12 3886 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3886 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3886) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3886.1, data_12_3886.2]

/-- Complete interval computation for depth 12, residue 3887. -/
theorem bounds_12_3887 : exactInterval 12 3887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3887 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3887) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3887 : oddCount 3887 12 = 6 ∧ acceleratedOrbit 12 3887 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3887 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3887) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3887.1, data_12_3887.2]

/-- Complete interval computation for depth 12, residue 3888. -/
theorem bounds_12_3888 : exactInterval 12 3888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3888 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3888) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3888 : oddCount 3888 12 = 5 ∧ acceleratedOrbit 12 3888 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3888 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3888) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3888.1, data_12_3888.2]

/-- Complete interval computation for depth 12, residue 3889. -/
theorem bounds_12_3889 : exactInterval 12 3889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3889 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3889) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3889 : oddCount 3889 12 = 4 ∧ acceleratedOrbit 12 3889 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3889 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3889) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3889.1, data_12_3889.2]

/-- Complete interval computation for depth 12, residue 3890. -/
theorem bounds_12_3890 : exactInterval 12 3890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3890 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3890) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3890 : oddCount 3890 12 = 4 ∧ acceleratedOrbit 12 3890 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3890 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3890) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3890.1, data_12_3890.2]

/-- Complete interval computation for depth 12, residue 3891. -/
theorem bounds_12_3891 : exactInterval 12 3891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3891 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3891) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3891 : oddCount 3891 12 = 4 ∧ acceleratedOrbit 12 3891 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3891 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3891) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3891.1, data_12_3891.2]

/-- Complete interval computation for depth 12, residue 3892. -/
theorem bounds_12_3892 : exactInterval 12 3892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3892 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3892) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3892 : oddCount 3892 12 = 5 ∧ acceleratedOrbit 12 3892 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3892 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3892) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3892.1, data_12_3892.2]

/-- Complete interval computation for depth 12, residue 3893. -/
theorem bounds_12_3893 : exactInterval 12 3893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3893 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3893) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3893 : oddCount 3893 12 = 5 ∧ acceleratedOrbit 12 3893 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3893 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3893) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3893.1, data_12_3893.2]

/-- Complete interval computation for depth 12, residue 3894. -/
theorem bounds_12_3894 : exactInterval 12 3894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3894 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3894) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3894 : oddCount 3894 12 = 7 ∧ acceleratedOrbit 12 3894 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3894 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3894) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3894.1, data_12_3894.2]

/-- Complete interval computation for depth 12, residue 3895. -/
theorem bounds_12_3895 : exactInterval 12 3895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3895 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3895) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3895 : oddCount 3895 12 = 7 ∧ acceleratedOrbit 12 3895 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3895 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3895) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3895.1, data_12_3895.2]

/-- Complete interval computation for depth 12, residue 3896. -/
theorem bounds_12_3896 : exactInterval 12 3896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3896 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3896) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3896 : oddCount 3896 12 = 6 ∧ acceleratedOrbit 12 3896 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3896 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3896) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3896.1, data_12_3896.2]

/-- Complete interval computation for depth 12, residue 3897. -/
theorem bounds_12_3897 : exactInterval 12 3897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3897 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3897) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3897 : oddCount 3897 12 = 6 ∧ acceleratedOrbit 12 3897 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3897 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3897) = 3 ^ 6 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3897.1, data_12_3897.2]

/-- Complete interval computation for depth 12, residue 3898. -/
theorem bounds_12_3898 : exactInterval 12 3898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3898 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3898) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3898 : oddCount 3898 12 = 6 ∧ acceleratedOrbit 12 3898 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3898 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3898) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3898.1, data_12_3898.2]

/-- Complete interval computation for depth 12, residue 3899. -/
theorem bounds_12_3899 : exactInterval 12 3899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3899 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3899) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3899 : oddCount 3899 12 = 6 ∧ acceleratedOrbit 12 3899 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3899 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3899) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3899.1, data_12_3899.2]

/-- Complete interval computation for depth 12, residue 3900. -/
theorem bounds_12_3900 : exactInterval 12 3900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3900 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3900) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3900 : oddCount 3900 12 = 6 ∧ acceleratedOrbit 12 3900 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3900 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3900) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3900.1, data_12_3900.2]

end Collatz.Research.StoppingAtlas.Batch0454
