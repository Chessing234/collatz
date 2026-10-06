import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0033

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1048. -/
theorem bounds_15_1048 : exactInterval 15 1048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1048 : oddCount 1048 15 = 6 ∧ acceleratedOrbit 15 1048 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1048) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1048.1, data_15_1048.2]

/-- Complete interval computation for depth 15, residue 1049. -/
theorem bounds_15_1049 : exactInterval 15 1049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1049 : oddCount 1049 15 = 8 ∧ acceleratedOrbit 15 1049 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1049) = 3 ^ 8 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1049.1, data_15_1049.2]

/-- Complete interval computation for depth 15, residue 1050. -/
theorem bounds_15_1050 : exactInterval 15 1050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1050 : oddCount 1050 15 = 6 ∧ acceleratedOrbit 15 1050 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1050) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1050.1, data_15_1050.2]

/-- Complete interval computation for depth 15, residue 1051. -/
theorem bounds_15_1051 : exactInterval 15 1051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1051 : oddCount 1051 15 = 11 ∧ acceleratedOrbit 15 1051 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1051) = 3 ^ 11 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1051.1, data_15_1051.2]

/-- Complete interval computation for depth 15, residue 1052. -/
theorem bounds_15_1052 : exactInterval 15 1052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1052 : oddCount 1052 15 = 9 ∧ acceleratedOrbit 15 1052 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1052) = 3 ^ 9 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1052.1, data_15_1052.2]

/-- Complete interval computation for depth 15, residue 1053. -/
theorem bounds_15_1053 : exactInterval 15 1053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1053 : oddCount 1053 15 = 9 ∧ acceleratedOrbit 15 1053 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1053) = 3 ^ 9 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1053.1, data_15_1053.2]

/-- Complete interval computation for depth 15, residue 1054. -/
theorem bounds_15_1054 : exactInterval 15 1054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1054 : oddCount 1054 15 = 9 ∧ acceleratedOrbit 15 1054 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1054) = 3 ^ 9 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1054.1, data_15_1054.2]

/-- Complete interval computation for depth 15, residue 1055. -/
theorem bounds_15_1055 : exactInterval 15 1055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1055 : oddCount 1055 15 = 12 ∧ acceleratedOrbit 15 1055 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1055) = 3 ^ 12 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1055.1, data_15_1055.2]

/-- Complete interval computation for depth 15, residue 1056. -/
theorem bounds_15_1056 : exactInterval 15 1056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1056 : oddCount 1056 15 = 6 ∧ acceleratedOrbit 15 1056 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1056) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1056.1, data_15_1056.2]

/-- Complete interval computation for depth 15, residue 1057. -/
theorem bounds_15_1057 : exactInterval 15 1057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1057 : oddCount 1057 15 = 9 ∧ acceleratedOrbit 15 1057 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1057) = 3 ^ 9 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1057.1, data_15_1057.2]

/-- Complete interval computation for depth 15, residue 1058. -/
theorem bounds_15_1058 : exactInterval 15 1058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1058 : oddCount 1058 15 = 6 ∧ acceleratedOrbit 15 1058 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1058) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1058.1, data_15_1058.2]

/-- Complete interval computation for depth 15, residue 1059. -/
theorem bounds_15_1059 : exactInterval 15 1059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1059 : oddCount 1059 15 = 6 ∧ acceleratedOrbit 15 1059 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1059) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1059.1, data_15_1059.2]

/-- Complete interval computation for depth 15, residue 1060. -/
theorem bounds_15_1060 : exactInterval 15 1060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1060 : oddCount 1060 15 = 8 ∧ acceleratedOrbit 15 1060 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1060) = 3 ^ 8 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1060.1, data_15_1060.2]

/-- Complete interval computation for depth 15, residue 1061. -/
theorem bounds_15_1061 : exactInterval 15 1061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1061 : oddCount 1061 15 = 8 ∧ acceleratedOrbit 15 1061 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1061) = 3 ^ 8 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1061.1, data_15_1061.2]

/-- Complete interval computation for depth 15, residue 1062. -/
theorem bounds_15_1062 : exactInterval 15 1062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1062 : oddCount 1062 15 = 8 ∧ acceleratedOrbit 15 1062 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1062) = 3 ^ 8 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1062.1, data_15_1062.2]

/-- Complete interval computation for depth 15, residue 1063. -/
theorem bounds_15_1063 : exactInterval 15 1063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1063 : oddCount 1063 15 = 9 ∧ acceleratedOrbit 15 1063 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1063) = 3 ^ 9 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1063.1, data_15_1063.2]

/-- Complete interval computation for depth 15, residue 1064. -/
theorem bounds_15_1064 : exactInterval 15 1064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1064 : oddCount 1064 15 = 6 ∧ acceleratedOrbit 15 1064 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1064) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1064.1, data_15_1064.2]

/-- Complete interval computation for depth 15, residue 1065. -/
theorem bounds_15_1065 : exactInterval 15 1065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1065 : oddCount 1065 15 = 9 ∧ acceleratedOrbit 15 1065 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1065) = 3 ^ 9 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1065.1, data_15_1065.2]

/-- Complete interval computation for depth 15, residue 1066. -/
theorem bounds_15_1066 : exactInterval 15 1066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1066 : oddCount 1066 15 = 6 ∧ acceleratedOrbit 15 1066 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1066) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1066.1, data_15_1066.2]

/-- Complete interval computation for depth 15, residue 1067. -/
theorem bounds_15_1067 : exactInterval 15 1067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1067 : oddCount 1067 15 = 9 ∧ acceleratedOrbit 15 1067 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1067) = 3 ^ 9 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1067.1, data_15_1067.2]

/-- Complete interval computation for depth 15, residue 1068. -/
theorem bounds_15_1068 : exactInterval 15 1068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1068 : oddCount 1068 15 = 5 ∧ acceleratedOrbit 15 1068 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1068) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1068.1, data_15_1068.2]

/-- Complete interval computation for depth 15, residue 1069. -/
theorem bounds_15_1069 : exactInterval 15 1069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1069 : oddCount 1069 15 = 5 ∧ acceleratedOrbit 15 1069 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1069) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1069.1, data_15_1069.2]

/-- Complete interval computation for depth 15, residue 1070. -/
theorem bounds_15_1070 : exactInterval 15 1070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1070 : oddCount 1070 15 = 5 ∧ acceleratedOrbit 15 1070 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1070) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1070.1, data_15_1070.2]

/-- Complete interval computation for depth 15, residue 1071. -/
theorem bounds_15_1071 : exactInterval 15 1071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1071 : oddCount 1071 15 = 10 ∧ acceleratedOrbit 15 1071 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1071) = 3 ^ 10 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1071.1, data_15_1071.2]

/-- Complete interval computation for depth 15, residue 1072. -/
theorem bounds_15_1072 : exactInterval 15 1072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1072 : oddCount 1072 15 = 6 ∧ acceleratedOrbit 15 1072 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1072) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1072.1, data_15_1072.2]

/-- Complete interval computation for depth 15, residue 1073. -/
theorem bounds_15_1073 : exactInterval 15 1073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1073 : oddCount 1073 15 = 5 ∧ acceleratedOrbit 15 1073 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1073) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1073.1, data_15_1073.2]

/-- Complete interval computation for depth 15, residue 1074. -/
theorem bounds_15_1074 : exactInterval 15 1074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1074 : oddCount 1074 15 = 5 ∧ acceleratedOrbit 15 1074 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1074) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1074.1, data_15_1074.2]

/-- Complete interval computation for depth 15, residue 1075. -/
theorem bounds_15_1075 : exactInterval 15 1075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1075 : oddCount 1075 15 = 5 ∧ acceleratedOrbit 15 1075 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1075) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1075.1, data_15_1075.2]

/-- Complete interval computation for depth 15, residue 1076. -/
theorem bounds_15_1076 : exactInterval 15 1076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1076 : oddCount 1076 15 = 6 ∧ acceleratedOrbit 15 1076 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1076) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1076.1, data_15_1076.2]

/-- Complete interval computation for depth 15, residue 1077. -/
theorem bounds_15_1077 : exactInterval 15 1077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1077 : oddCount 1077 15 = 6 ∧ acceleratedOrbit 15 1077 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1077) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1077.1, data_15_1077.2]

/-- Complete interval computation for depth 15, residue 1078. -/
theorem bounds_15_1078 : exactInterval 15 1078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1078 : oddCount 1078 15 = 9 ∧ acceleratedOrbit 15 1078 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1078) = 3 ^ 9 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1078.1, data_15_1078.2]

/-- Complete interval computation for depth 15, residue 1079. -/
theorem bounds_15_1079 : exactInterval 15 1079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1079 : oddCount 1079 15 = 9 ∧ acceleratedOrbit 15 1079 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1079) = 3 ^ 9 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1079.1, data_15_1079.2]

/-- Complete interval computation for depth 15, residue 1080. -/
theorem bounds_15_1080 : exactInterval 15 1080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1080 : oddCount 1080 15 = 7 ∧ acceleratedOrbit 15 1080 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1080) = 3 ^ 7 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1080.1, data_15_1080.2]

end Collatz.Research.PassageAtlas.Batch0033
