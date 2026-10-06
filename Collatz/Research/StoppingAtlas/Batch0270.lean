import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0270

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1059. -/
theorem bounds_12_1059 : exactInterval 12 1059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1059 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1059) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1059 : oddCount 1059 12 = 3 ∧ acceleratedOrbit 12 1059 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1059 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1059) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1059.1, data_12_1059.2]

/-- Complete interval computation for depth 12, residue 1060. -/
theorem bounds_12_1060 : exactInterval 12 1060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1060 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1060) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1060 : oddCount 1060 12 = 6 ∧ acceleratedOrbit 12 1060 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1060 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1060) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1060.1, data_12_1060.2]

/-- Complete interval computation for depth 12, residue 1061. -/
theorem bounds_12_1061 : exactInterval 12 1061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1061 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1061) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1061 : oddCount 1061 12 = 6 ∧ acceleratedOrbit 12 1061 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1061 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1061) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1061.1, data_12_1061.2]

/-- Complete interval computation for depth 12, residue 1062. -/
theorem bounds_12_1062 : exactInterval 12 1062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1062 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1062) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1062 : oddCount 1062 12 = 6 ∧ acceleratedOrbit 12 1062 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1062 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1062) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1062.1, data_12_1062.2]

/-- Complete interval computation for depth 12, residue 1063. -/
theorem bounds_12_1063 : exactInterval 12 1063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1063 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1063) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1063 : oddCount 1063 12 = 7 ∧ acceleratedOrbit 12 1063 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1063 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1063) = 3 ^ 7 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1063.1, data_12_1063.2]

/-- Complete interval computation for depth 12, residue 1064. -/
theorem bounds_12_1064 : exactInterval 12 1064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1064 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1064) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1064 : oddCount 1064 12 = 4 ∧ acceleratedOrbit 12 1064 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1064 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1064) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1064.1, data_12_1064.2]

/-- Complete interval computation for depth 12, residue 1065. -/
theorem bounds_12_1065 : exactInterval 12 1065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1065 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1065) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1065 : oddCount 1065 12 = 8 ∧ acceleratedOrbit 12 1065 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1065 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1065) = 3 ^ 8 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1065.1, data_12_1065.2]

/-- Complete interval computation for depth 12, residue 1066. -/
theorem bounds_12_1066 : exactInterval 12 1066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1066 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1066) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1066 : oddCount 1066 12 = 4 ∧ acceleratedOrbit 12 1066 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1066 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1066) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1066.1, data_12_1066.2]

/-- Complete interval computation for depth 12, residue 1067. -/
theorem bounds_12_1067 : exactInterval 12 1067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1067 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1067) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1067 : oddCount 1067 12 = 6 ∧ acceleratedOrbit 12 1067 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1067 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1067) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1067.1, data_12_1067.2]

/-- Complete interval computation for depth 12, residue 1068. -/
theorem bounds_12_1068 : exactInterval 12 1068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1068 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1068) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1068 : oddCount 1068 12 = 5 ∧ acceleratedOrbit 12 1068 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1068 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1068) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1068.1, data_12_1068.2]

/-- Complete interval computation for depth 12, residue 1069. -/
theorem bounds_12_1069 : exactInterval 12 1069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1069 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1069) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1069 : oddCount 1069 12 = 5 ∧ acceleratedOrbit 12 1069 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1069 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1069) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1069.1, data_12_1069.2]

/-- Complete interval computation for depth 12, residue 1070. -/
theorem bounds_12_1070 : exactInterval 12 1070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1070 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1070) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1070 : oddCount 1070 12 = 5 ∧ acceleratedOrbit 12 1070 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1070 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1070) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1070.1, data_12_1070.2]

/-- Complete interval computation for depth 12, residue 1071. -/
theorem bounds_12_1071 : exactInterval 12 1071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1071 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1071) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1071 : oddCount 1071 12 = 8 ∧ acceleratedOrbit 12 1071 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1071 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1071) = 3 ^ 8 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1071.1, data_12_1071.2]

/-- Complete interval computation for depth 12, residue 1072. -/
theorem bounds_12_1072 : exactInterval 12 1072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1072 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1072) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1072 : oddCount 1072 12 = 4 ∧ acceleratedOrbit 12 1072 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1072 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1072) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1072.1, data_12_1072.2]

/-- Complete interval computation for depth 12, residue 1073. -/
theorem bounds_12_1073 : exactInterval 12 1073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1073 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1073) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1073 : oddCount 1073 12 = 5 ∧ acceleratedOrbit 12 1073 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1073 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1073) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1073.1, data_12_1073.2]

/-- Complete interval computation for depth 12, residue 1074. -/
theorem bounds_12_1074 : exactInterval 12 1074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1074 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1074) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1074 : oddCount 1074 12 = 5 ∧ acceleratedOrbit 12 1074 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1074 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1074) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1074.1, data_12_1074.2]

end Collatz.Research.StoppingAtlas.Batch0270
