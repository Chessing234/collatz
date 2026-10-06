import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0863

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6072. -/
theorem bounds_13_6072 : exactInterval 13 6072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6072 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6072) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6072 : oddCount 6072 13 = 6 ∧ acceleratedOrbit 13 6072 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6072 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6072) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6072.1, data_13_6072.2]

/-- Complete interval computation for depth 13, residue 6073. -/
theorem bounds_13_6073 : exactInterval 13 6073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6073 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6073) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6073 : oddCount 6073 13 = 6 ∧ acceleratedOrbit 13 6073 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6073 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6073) = 3 ^ 6 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6073.1, data_13_6073.2]

/-- Complete interval computation for depth 13, residue 6074. -/
theorem bounds_13_6074 : exactInterval 13 6074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6074 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6074) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6074 : oddCount 6074 13 = 6 ∧ acceleratedOrbit 13 6074 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6074 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6074) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6074.1, data_13_6074.2]

/-- Complete interval computation for depth 13, residue 6075. -/
theorem bounds_13_6075 : exactInterval 13 6075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6075 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6075) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6075 : oddCount 6075 13 = 6 ∧ acceleratedOrbit 13 6075 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6075 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6075) = 3 ^ 6 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6075.1, data_13_6075.2]

/-- Complete interval computation for depth 13, residue 6076. -/
theorem bounds_13_6076 : exactInterval 13 6076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6076 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6076) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6076 : oddCount 6076 13 = 8 ∧ acceleratedOrbit 13 6076 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6076 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6076) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6076.1, data_13_6076.2]

/-- Complete interval computation for depth 13, residue 6077. -/
theorem bounds_13_6077 : exactInterval 13 6077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6077 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6077) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6077 : oddCount 6077 13 = 8 ∧ acceleratedOrbit 13 6077 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6077 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6077) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6077.1, data_13_6077.2]

/-- Complete interval computation for depth 13, residue 6078. -/
theorem bounds_13_6078 : exactInterval 13 6078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6078 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6078) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6078 : oddCount 6078 13 = 8 ∧ acceleratedOrbit 13 6078 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6078 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6078) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6078.1, data_13_6078.2]

/-- Complete interval computation for depth 13, residue 6079. -/
theorem bounds_13_6079 : exactInterval 13 6079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6079 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6079) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6079 : oddCount 6079 13 = 9 ∧ acceleratedOrbit 13 6079 = 14609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6079 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6079) = 3 ^ 9 * m + 14609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6079.1, data_13_6079.2]

/-- Complete interval computation for depth 13, residue 6080. -/
theorem bounds_13_6080 : exactInterval 13 6080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6080 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6080) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6080 : oddCount 6080 13 = 5 ∧ acceleratedOrbit 13 6080 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6080 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6080) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6080.1, data_13_6080.2]

/-- Complete interval computation for depth 13, residue 6081. -/
theorem bounds_13_6081 : exactInterval 13 6081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6081 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6081) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6081 : oddCount 6081 13 = 6 ∧ acceleratedOrbit 13 6081 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6081 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6081) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6081.1, data_13_6081.2]

/-- Complete interval computation for depth 13, residue 6082. -/
theorem bounds_13_6082 : exactInterval 13 6082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6082 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6082) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6082 : oddCount 6082 13 = 7 ∧ acceleratedOrbit 13 6082 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6082 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6082) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6082.1, data_13_6082.2]

/-- Complete interval computation for depth 13, residue 6083. -/
theorem bounds_13_6083 : exactInterval 13 6083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6083 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6083) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6083 : oddCount 6083 13 = 7 ∧ acceleratedOrbit 13 6083 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6083 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6083) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6083.1, data_13_6083.2]

/-- Complete interval computation for depth 13, residue 6084. -/
theorem bounds_13_6084 : exactInterval 13 6084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6084 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6084) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6084 : oddCount 6084 13 = 5 ∧ acceleratedOrbit 13 6084 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6084 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6084) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6084.1, data_13_6084.2]

/-- Complete interval computation for depth 13, residue 6085. -/
theorem bounds_13_6085 : exactInterval 13 6085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6085 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6085) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6085 : oddCount 6085 13 = 5 ∧ acceleratedOrbit 13 6085 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6085 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6085) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6085.1, data_13_6085.2]

/-- Complete interval computation for depth 13, residue 6086. -/
theorem bounds_13_6086 : exactInterval 13 6086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6086 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6086) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6086 : oddCount 6086 13 = 5 ∧ acceleratedOrbit 13 6086 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6086 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6086) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6086.1, data_13_6086.2]

end Collatz.Research.StoppingAtlas.Batch0863
