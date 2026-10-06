import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0136

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1049. -/
theorem bounds_11_1049 : exactInterval 11 1049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1049 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1049) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1049 : oddCount 1049 11 = 7 ∧ acceleratedOrbit 11 1049 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1049 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1049) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1049.1, data_11_1049.2]

/-- Complete interval computation for depth 11, residue 1050. -/
theorem bounds_11_1050 : exactInterval 11 1050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1050 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1050) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1050 : oddCount 1050 11 = 3 ∧ acceleratedOrbit 11 1050 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1050 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1050) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1050.1, data_11_1050.2]

/-- Complete interval computation for depth 11, residue 1051. -/
theorem bounds_11_1051 : exactInterval 11 1051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1051 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1051) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1051 : oddCount 1051 11 = 9 ∧ acceleratedOrbit 11 1051 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1051 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1051) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1051.1, data_11_1051.2]

/-- Complete interval computation for depth 11, residue 1052. -/
theorem bounds_11_1052 : exactInterval 11 1052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1052 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1052) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1052 : oddCount 1052 11 = 6 ∧ acceleratedOrbit 11 1052 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1052 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1052) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1052.1, data_11_1052.2]

/-- Complete interval computation for depth 11, residue 1053. -/
theorem bounds_11_1053 : exactInterval 11 1053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1053 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1053) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1053 : oddCount 1053 11 = 6 ∧ acceleratedOrbit 11 1053 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1053 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1053) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1053.1, data_11_1053.2]

/-- Complete interval computation for depth 11, residue 1054. -/
theorem bounds_11_1054 : exactInterval 11 1054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1054 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1054) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1054 : oddCount 1054 11 = 6 ∧ acceleratedOrbit 11 1054 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1054 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1054) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1054.1, data_11_1054.2]

/-- Complete interval computation for depth 11, residue 1055. -/
theorem bounds_11_1055 : exactInterval 11 1055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1055 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1055) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1055 : oddCount 1055 11 = 9 ∧ acceleratedOrbit 11 1055 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1055 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1055) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1055.1, data_11_1055.2]

/-- Complete interval computation for depth 11, residue 1056. -/
theorem bounds_11_1056 : exactInterval 11 1056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1056 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1056) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1056 : oddCount 1056 11 = 4 ∧ acceleratedOrbit 11 1056 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1056 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1056) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1056.1, data_11_1056.2]

/-- Complete interval computation for depth 11, residue 1057. -/
theorem bounds_11_1057 : exactInterval 11 1057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1057 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1057) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1057 : oddCount 1057 11 = 7 ∧ acceleratedOrbit 11 1057 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1057 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1057) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1057.1, data_11_1057.2]

/-- Complete interval computation for depth 11, residue 1058. -/
theorem bounds_11_1058 : exactInterval 11 1058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1058 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1058) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1058 : oddCount 1058 11 = 3 ∧ acceleratedOrbit 11 1058 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1058 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1058) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1058.1, data_11_1058.2]

/-- Complete interval computation for depth 11, residue 1059. -/
theorem bounds_11_1059 : exactInterval 11 1059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1059 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1059) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1059 : oddCount 1059 11 = 3 ∧ acceleratedOrbit 11 1059 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1059 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1059) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1059.1, data_11_1059.2]

/-- Complete interval computation for depth 11, residue 1060. -/
theorem bounds_11_1060 : exactInterval 11 1060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1060 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1060) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1060 : oddCount 1060 11 = 6 ∧ acceleratedOrbit 11 1060 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1060 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1060) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1060.1, data_11_1060.2]

/-- Complete interval computation for depth 11, residue 1061. -/
theorem bounds_11_1061 : exactInterval 11 1061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1061 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1061) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1061 : oddCount 1061 11 = 6 ∧ acceleratedOrbit 11 1061 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1061 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1061) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1061.1, data_11_1061.2]

/-- Complete interval computation for depth 11, residue 1062. -/
theorem bounds_11_1062 : exactInterval 11 1062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1062 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1062) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1062 : oddCount 1062 11 = 6 ∧ acceleratedOrbit 11 1062 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1062 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1062) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1062.1, data_11_1062.2]

/-- Complete interval computation for depth 11, residue 1063. -/
theorem bounds_11_1063 : exactInterval 11 1063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1063 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1063) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1063 : oddCount 1063 11 = 6 ∧ acceleratedOrbit 11 1063 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1063 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1063) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1063.1, data_11_1063.2]

end Collatz.Research.StoppingAtlas.Batch0136
