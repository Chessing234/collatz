import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0269

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1044. -/
theorem bounds_12_1044 : exactInterval 12 1044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1044 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1044) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1044 : oddCount 1044 12 = 3 ∧ acceleratedOrbit 12 1044 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1044 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1044) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1044.1, data_12_1044.2]

/-- Complete interval computation for depth 12, residue 1045. -/
theorem bounds_12_1045 : exactInterval 12 1045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1045 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1045) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1045 : oddCount 1045 12 = 3 ∧ acceleratedOrbit 12 1045 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1045 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1045) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1045.1, data_12_1045.2]

/-- Complete interval computation for depth 12, residue 1046. -/
theorem bounds_12_1046 : exactInterval 12 1046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1046 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1046) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1046 : oddCount 1046 12 = 6 ∧ acceleratedOrbit 12 1046 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1046 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1046) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1046.1, data_12_1046.2]

/-- Complete interval computation for depth 12, residue 1047. -/
theorem bounds_12_1047 : exactInterval 12 1047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1047 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1047) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1047 : oddCount 1047 12 = 6 ∧ acceleratedOrbit 12 1047 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1047 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1047) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1047.1, data_12_1047.2]

/-- Complete interval computation for depth 12, residue 1048. -/
theorem bounds_12_1048 : exactInterval 12 1048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1048 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1048) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1048 : oddCount 1048 12 = 3 ∧ acceleratedOrbit 12 1048 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1048 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1048) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1048.1, data_12_1048.2]

/-- Complete interval computation for depth 12, residue 1049. -/
theorem bounds_12_1049 : exactInterval 12 1049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1049 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1049) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1049 : oddCount 1049 12 = 7 ∧ acceleratedOrbit 12 1049 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1049 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1049) = 3 ^ 7 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1049.1, data_12_1049.2]

/-- Complete interval computation for depth 12, residue 1050. -/
theorem bounds_12_1050 : exactInterval 12 1050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1050 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1050) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1050 : oddCount 1050 12 = 3 ∧ acceleratedOrbit 12 1050 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1050 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1050) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1050.1, data_12_1050.2]

/-- Complete interval computation for depth 12, residue 1051. -/
theorem bounds_12_1051 : exactInterval 12 1051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1051 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1051) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1051 : oddCount 1051 12 = 10 ∧ acceleratedOrbit 12 1051 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1051 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1051) = 3 ^ 10 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1051.1, data_12_1051.2]

/-- Complete interval computation for depth 12, residue 1052. -/
theorem bounds_12_1052 : exactInterval 12 1052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1052 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1052) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1052 : oddCount 1052 12 = 7 ∧ acceleratedOrbit 12 1052 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1052 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1052) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1052.1, data_12_1052.2]

/-- Complete interval computation for depth 12, residue 1053. -/
theorem bounds_12_1053 : exactInterval 12 1053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1053 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1053) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1053 : oddCount 1053 12 = 7 ∧ acceleratedOrbit 12 1053 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1053 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1053) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1053.1, data_12_1053.2]

/-- Complete interval computation for depth 12, residue 1054. -/
theorem bounds_12_1054 : exactInterval 12 1054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1054 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1054) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1054 : oddCount 1054 12 = 7 ∧ acceleratedOrbit 12 1054 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1054 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1054) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1054.1, data_12_1054.2]

/-- Complete interval computation for depth 12, residue 1055. -/
theorem bounds_12_1055 : exactInterval 12 1055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1055 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1055) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1055 : oddCount 1055 12 = 10 ∧ acceleratedOrbit 12 1055 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1055 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1055) = 3 ^ 10 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1055.1, data_12_1055.2]

/-- Complete interval computation for depth 12, residue 1056. -/
theorem bounds_12_1056 : exactInterval 12 1056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1056 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1056) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1056 : oddCount 1056 12 = 4 ∧ acceleratedOrbit 12 1056 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1056 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1056) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1056.1, data_12_1056.2]

/-- Complete interval computation for depth 12, residue 1057. -/
theorem bounds_12_1057 : exactInterval 12 1057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1057 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1057) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1057 : oddCount 1057 12 = 8 ∧ acceleratedOrbit 12 1057 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1057 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1057) = 3 ^ 8 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1057.1, data_12_1057.2]

/-- Complete interval computation for depth 12, residue 1058. -/
theorem bounds_12_1058 : exactInterval 12 1058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1058 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1058) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1058 : oddCount 1058 12 = 3 ∧ acceleratedOrbit 12 1058 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1058 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1058) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1058.1, data_12_1058.2]

end Collatz.Research.StoppingAtlas.Batch0269
