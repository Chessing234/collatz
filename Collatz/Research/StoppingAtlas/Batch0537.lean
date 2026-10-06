import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0537

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1064. -/
theorem bounds_13_1064 : exactInterval 13 1064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1064 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1064) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1064 : oddCount 1064 13 = 4 ∧ acceleratedOrbit 13 1064 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1064 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1064) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1064.1, data_13_1064.2]

/-- Complete interval computation for depth 13, residue 1065. -/
theorem bounds_13_1065 : exactInterval 13 1065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1065 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1065) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1065 : oddCount 1065 13 = 9 ∧ acceleratedOrbit 13 1065 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1065 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1065) = 3 ^ 9 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1065.1, data_13_1065.2]

/-- Complete interval computation for depth 13, residue 1066. -/
theorem bounds_13_1066 : exactInterval 13 1066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1066 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1066) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1066 : oddCount 1066 13 = 4 ∧ acceleratedOrbit 13 1066 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1066 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1066) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1066.1, data_13_1066.2]

/-- Complete interval computation for depth 13, residue 1067. -/
theorem bounds_13_1067 : exactInterval 13 1067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1067 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1067) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1067 : oddCount 1067 13 = 7 ∧ acceleratedOrbit 13 1067 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1067 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1067) = 3 ^ 7 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1067.1, data_13_1067.2]

/-- Complete interval computation for depth 13, residue 1068. -/
theorem bounds_13_1068 : exactInterval 13 1068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1068 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1068) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1068 : oddCount 1068 13 = 5 ∧ acceleratedOrbit 13 1068 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1068 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1068) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1068.1, data_13_1068.2]

/-- Complete interval computation for depth 13, residue 1069. -/
theorem bounds_13_1069 : exactInterval 13 1069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1069 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1069) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1069 : oddCount 1069 13 = 5 ∧ acceleratedOrbit 13 1069 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1069 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1069) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1069.1, data_13_1069.2]

/-- Complete interval computation for depth 13, residue 1070. -/
theorem bounds_13_1070 : exactInterval 13 1070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1070 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1070) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1070 : oddCount 1070 13 = 5 ∧ acceleratedOrbit 13 1070 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1070 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1070) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1070.1, data_13_1070.2]

/-- Complete interval computation for depth 13, residue 1071. -/
theorem bounds_13_1071 : exactInterval 13 1071 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1071 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1071) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1071 : oddCount 1071 13 = 8 ∧ acceleratedOrbit 13 1071 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1071 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1071) = 3 ^ 8 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1071.1, data_13_1071.2]

/-- Complete interval computation for depth 13, residue 1072. -/
theorem bounds_13_1072 : exactInterval 13 1072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1072 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1072) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1072 : oddCount 1072 13 = 4 ∧ acceleratedOrbit 13 1072 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1072 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1072) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1072.1, data_13_1072.2]

/-- Complete interval computation for depth 13, residue 1073. -/
theorem bounds_13_1073 : exactInterval 13 1073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1073 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1073) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1073 : oddCount 1073 13 = 5 ∧ acceleratedOrbit 13 1073 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1073 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1073) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1073.1, data_13_1073.2]

/-- Complete interval computation for depth 13, residue 1074. -/
theorem bounds_13_1074 : exactInterval 13 1074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1074 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1074) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1074 : oddCount 1074 13 = 5 ∧ acceleratedOrbit 13 1074 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1074 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1074) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1074.1, data_13_1074.2]

/-- Complete interval computation for depth 13, residue 1075. -/
theorem bounds_13_1075 : exactInterval 13 1075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1075 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1075) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1075 : oddCount 1075 13 = 5 ∧ acceleratedOrbit 13 1075 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1075 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1075) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1075.1, data_13_1075.2]

/-- Complete interval computation for depth 13, residue 1076. -/
theorem bounds_13_1076 : exactInterval 13 1076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1076 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1076) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1076 : oddCount 1076 13 = 4 ∧ acceleratedOrbit 13 1076 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1076 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1076) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1076.1, data_13_1076.2]

/-- Complete interval computation for depth 13, residue 1077. -/
theorem bounds_13_1077 : exactInterval 13 1077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1077 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1077) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1077 : oddCount 1077 13 = 4 ∧ acceleratedOrbit 13 1077 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1077 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1077) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1077.1, data_13_1077.2]

/-- Complete interval computation for depth 13, residue 1078. -/
theorem bounds_13_1078 : exactInterval 13 1078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1078 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1078) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1078 : oddCount 1078 13 = 8 ∧ acceleratedOrbit 13 1078 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1078 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1078) = 3 ^ 8 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1078.1, data_13_1078.2]

/-- Complete interval computation for depth 13, residue 1079. -/
theorem bounds_13_1079 : exactInterval 13 1079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1079 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1079) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1079 : oddCount 1079 13 = 8 ∧ acceleratedOrbit 13 1079 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1079 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1079) = 3 ^ 8 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1079.1, data_13_1079.2]

end Collatz.Research.StoppingAtlas.Batch0537
