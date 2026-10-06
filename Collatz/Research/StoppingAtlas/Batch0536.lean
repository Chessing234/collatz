import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0536

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1049. -/
theorem bounds_13_1049 : exactInterval 13 1049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1049 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1049) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1049 : oddCount 1049 13 = 7 ∧ acceleratedOrbit 13 1049 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1049 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1049) = 3 ^ 7 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1049.1, data_13_1049.2]

/-- Complete interval computation for depth 13, residue 1050. -/
theorem bounds_13_1050 : exactInterval 13 1050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1050 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1050) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1050 : oddCount 1050 13 = 4 ∧ acceleratedOrbit 13 1050 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1050 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1050) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1050.1, data_13_1050.2]

/-- Complete interval computation for depth 13, residue 1051. -/
theorem bounds_13_1051 : exactInterval 13 1051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1051 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1051) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1051 : oddCount 1051 13 = 11 ∧ acceleratedOrbit 13 1051 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1051 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1051) = 3 ^ 11 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1051.1, data_13_1051.2]

/-- Complete interval computation for depth 13, residue 1052. -/
theorem bounds_13_1052 : exactInterval 13 1052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1052 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1052) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1052 : oddCount 1052 13 = 7 ∧ acceleratedOrbit 13 1052 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1052 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1052) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1052.1, data_13_1052.2]

/-- Complete interval computation for depth 13, residue 1053. -/
theorem bounds_13_1053 : exactInterval 13 1053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1053 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1053) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1053 : oddCount 1053 13 = 7 ∧ acceleratedOrbit 13 1053 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1053 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1053) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1053.1, data_13_1053.2]

/-- Complete interval computation for depth 13, residue 1054. -/
theorem bounds_13_1054 : exactInterval 13 1054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1054 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1054) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1054 : oddCount 1054 13 = 7 ∧ acceleratedOrbit 13 1054 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1054 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1054) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1054.1, data_13_1054.2]

/-- Complete interval computation for depth 13, residue 1055. -/
theorem bounds_13_1055 : exactInterval 13 1055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1055 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1055) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1055 : oddCount 1055 13 = 11 ∧ acceleratedOrbit 13 1055 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1055 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1055) = 3 ^ 11 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1055.1, data_13_1055.2]

/-- Complete interval computation for depth 13, residue 1056. -/
theorem bounds_13_1056 : exactInterval 13 1056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1056 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1056) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1056 : oddCount 1056 13 = 4 ∧ acceleratedOrbit 13 1056 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1056 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1056) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1056.1, data_13_1056.2]

/-- Complete interval computation for depth 13, residue 1057. -/
theorem bounds_13_1057 : exactInterval 13 1057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1057 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1057) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1057 : oddCount 1057 13 = 8 ∧ acceleratedOrbit 13 1057 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1057 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1057) = 3 ^ 8 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1057.1, data_13_1057.2]

/-- Complete interval computation for depth 13, residue 1058. -/
theorem bounds_13_1058 : exactInterval 13 1058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1058 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1058) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1058 : oddCount 1058 13 = 4 ∧ acceleratedOrbit 13 1058 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1058 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1058) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1058.1, data_13_1058.2]

/-- Complete interval computation for depth 13, residue 1059. -/
theorem bounds_13_1059 : exactInterval 13 1059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1059 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1059) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1059 : oddCount 1059 13 = 4 ∧ acceleratedOrbit 13 1059 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1059 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1059) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1059.1, data_13_1059.2]

/-- Complete interval computation for depth 13, residue 1060. -/
theorem bounds_13_1060 : exactInterval 13 1060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1060 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1060) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1060 : oddCount 1060 13 = 6 ∧ acceleratedOrbit 13 1060 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1060 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1060) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1060.1, data_13_1060.2]

/-- Complete interval computation for depth 13, residue 1061. -/
theorem bounds_13_1061 : exactInterval 13 1061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1061 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1061) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1061 : oddCount 1061 13 = 6 ∧ acceleratedOrbit 13 1061 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1061 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1061) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1061.1, data_13_1061.2]

/-- Complete interval computation for depth 13, residue 1062. -/
theorem bounds_13_1062 : exactInterval 13 1062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1062 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1062) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1062 : oddCount 1062 13 = 6 ∧ acceleratedOrbit 13 1062 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1062 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1062) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1062.1, data_13_1062.2]

/-- Complete interval computation for depth 13, residue 1063. -/
theorem bounds_13_1063 : exactInterval 13 1063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1063 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1063) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1063 : oddCount 1063 13 = 8 ∧ acceleratedOrbit 13 1063 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1063 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1063) = 3 ^ 8 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1063.1, data_13_1063.2]

end Collatz.Research.StoppingAtlas.Batch0536
