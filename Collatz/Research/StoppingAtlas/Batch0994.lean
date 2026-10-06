import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0994

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8084. -/
theorem bounds_13_8084 : exactInterval 13 8084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8084 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8084) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8084 : oddCount 8084 13 = 6 ∧ acceleratedOrbit 13 8084 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8084 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8084) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8084.1, data_13_8084.2]

/-- Complete interval computation for depth 13, residue 8085. -/
theorem bounds_13_8085 : exactInterval 13 8085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8085 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8085) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8085 : oddCount 8085 13 = 6 ∧ acceleratedOrbit 13 8085 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8085 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8085) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8085.1, data_13_8085.2]

/-- Complete interval computation for depth 13, residue 8086. -/
theorem bounds_13_8086 : exactInterval 13 8086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8086 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8086) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8086 : oddCount 8086 13 = 4 ∧ acceleratedOrbit 13 8086 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8086 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8086) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8086.1, data_13_8086.2]

/-- Complete interval computation for depth 13, residue 8087. -/
theorem bounds_13_8087 : exactInterval 13 8087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8087 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8087) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8087 : oddCount 8087 13 = 4 ∧ acceleratedOrbit 13 8087 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8087 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8087) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8087.1, data_13_8087.2]

/-- Complete interval computation for depth 13, residue 8088. -/
theorem bounds_13_8088 : exactInterval 13 8088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8088 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8088) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8088 : oddCount 8088 13 = 6 ∧ acceleratedOrbit 13 8088 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8088 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8088) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8088.1, data_13_8088.2]

/-- Complete interval computation for depth 13, residue 8089. -/
theorem bounds_13_8089 : exactInterval 13 8089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8089 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8089) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8089 : oddCount 8089 13 = 4 ∧ acceleratedOrbit 13 8089 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8089 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8089) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8089.1, data_13_8089.2]

/-- Complete interval computation for depth 13, residue 8090. -/
theorem bounds_13_8090 : exactInterval 13 8090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8090 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8090) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8090 : oddCount 8090 13 = 6 ∧ acceleratedOrbit 13 8090 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8090 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8090) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8090.1, data_13_8090.2]

/-- Complete interval computation for depth 13, residue 8091. -/
theorem bounds_13_8091 : exactInterval 13 8091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8091 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8091) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8091 : oddCount 8091 13 = 8 ∧ acceleratedOrbit 13 8091 = 6482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8091 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8091) = 3 ^ 8 * m + 6482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8091.1, data_13_8091.2]

/-- Complete interval computation for depth 13, residue 8092. -/
theorem bounds_13_8092 : exactInterval 13 8092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8092 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8092) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8092 : oddCount 8092 13 = 7 ∧ acceleratedOrbit 13 8092 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8092 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8092) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8092.1, data_13_8092.2]

/-- Complete interval computation for depth 13, residue 8093. -/
theorem bounds_13_8093 : exactInterval 13 8093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8093 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8093) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8093 : oddCount 8093 13 = 7 ∧ acceleratedOrbit 13 8093 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8093 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8093) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8093.1, data_13_8093.2]

/-- Complete interval computation for depth 13, residue 8094. -/
theorem bounds_13_8094 : exactInterval 13 8094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8094 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8094) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8094 : oddCount 8094 13 = 7 ∧ acceleratedOrbit 13 8094 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8094 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8094) = 3 ^ 7 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8094.1, data_13_8094.2]

/-- Complete interval computation for depth 13, residue 8095. -/
theorem bounds_13_8095 : exactInterval 13 8095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8095 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8095) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8095 : oddCount 8095 13 = 9 ∧ acceleratedOrbit 13 8095 = 19453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8095 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8095) = 3 ^ 9 * m + 19453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8095.1, data_13_8095.2]

/-- Complete interval computation for depth 13, residue 8096. -/
theorem bounds_13_8096 : exactInterval 13 8096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8096 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8096) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8096 : oddCount 8096 13 = 6 ∧ acceleratedOrbit 13 8096 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8096 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8096) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8096.1, data_13_8096.2]

/-- Complete interval computation for depth 13, residue 8097. -/
theorem bounds_13_8097 : exactInterval 13 8097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8097 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8097) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8097 : oddCount 8097 13 = 6 ∧ acceleratedOrbit 13 8097 = 721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8097 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8097) = 3 ^ 6 * m + 721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8097.1, data_13_8097.2]

/-- Complete interval computation for depth 13, residue 8098. -/
theorem bounds_13_8098 : exactInterval 13 8098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8098 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8098) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8098 : oddCount 8098 13 = 6 ∧ acceleratedOrbit 13 8098 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8098 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8098) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8098.1, data_13_8098.2]

end Collatz.Research.StoppingAtlas.Batch0994
