import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0217

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7077. -/
theorem bounds_15_7077 : exactInterval 15 7077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7077 : oddCount 7077 15 = 9 ∧ acceleratedOrbit 15 7077 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7077) = 3 ^ 9 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7077.1, data_15_7077.2]

/-- Complete interval computation for depth 15, residue 7078. -/
theorem bounds_15_7078 : exactInterval 15 7078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7078 : oddCount 7078 15 = 9 ∧ acceleratedOrbit 15 7078 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7078) = 3 ^ 9 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7078.1, data_15_7078.2]

/-- Complete interval computation for depth 15, residue 7079. -/
theorem bounds_15_7079 : exactInterval 15 7079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7079 : oddCount 7079 15 = 10 ∧ acceleratedOrbit 15 7079 = 12761 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7079) = 3 ^ 10 * m + 12761 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7079.1, data_15_7079.2]

/-- Complete interval computation for depth 15, residue 7080. -/
theorem bounds_15_7080 : exactInterval 15 7080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7080 : oddCount 7080 15 = 6 ∧ acceleratedOrbit 15 7080 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7080) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7080.1, data_15_7080.2]

/-- Complete interval computation for depth 15, residue 7081. -/
theorem bounds_15_7081 : exactInterval 15 7081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7081 : oddCount 7081 15 = 10 ∧ acceleratedOrbit 15 7081 = 12764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7081) = 3 ^ 10 * m + 12764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7081.1, data_15_7081.2]

/-- Complete interval computation for depth 15, residue 7082. -/
theorem bounds_15_7082 : exactInterval 15 7082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7082 : oddCount 7082 15 = 6 ∧ acceleratedOrbit 15 7082 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7082) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7082.1, data_15_7082.2]

/-- Complete interval computation for depth 15, residue 7083. -/
theorem bounds_15_7083 : exactInterval 15 7083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7083 : oddCount 7083 15 = 7 ∧ acceleratedOrbit 15 7083 = 473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7083) = 3 ^ 7 * m + 473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7083.1, data_15_7083.2]

/-- Complete interval computation for depth 15, residue 7084. -/
theorem bounds_15_7084 : exactInterval 15 7084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7084 : oddCount 7084 15 = 8 ∧ acceleratedOrbit 15 7084 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7084) = 3 ^ 8 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7084.1, data_15_7084.2]

/-- Complete interval computation for depth 15, residue 7085. -/
theorem bounds_15_7085 : exactInterval 15 7085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7085 : oddCount 7085 15 = 8 ∧ acceleratedOrbit 15 7085 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7085) = 3 ^ 8 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7085.1, data_15_7085.2]

/-- Complete interval computation for depth 15, residue 7086. -/
theorem bounds_15_7086 : exactInterval 15 7086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7086 : oddCount 7086 15 = 8 ∧ acceleratedOrbit 15 7086 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7086) = 3 ^ 8 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7086.1, data_15_7086.2]

/-- Complete interval computation for depth 15, residue 7087. -/
theorem bounds_15_7087 : exactInterval 15 7087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7087 : oddCount 7087 15 = 8 ∧ acceleratedOrbit 15 7087 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7087) = 3 ^ 8 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7087.1, data_15_7087.2]

/-- Complete interval computation for depth 15, residue 7088. -/
theorem bounds_15_7088 : exactInterval 15 7088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7088 : oddCount 7088 15 = 7 ∧ acceleratedOrbit 15 7088 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7088) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7088.1, data_15_7088.2]

/-- Complete interval computation for depth 15, residue 7089. -/
theorem bounds_15_7089 : exactInterval 15 7089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7089 : oddCount 7089 15 = 7 ∧ acceleratedOrbit 15 7089 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7089) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7089.1, data_15_7089.2]

/-- Complete interval computation for depth 15, residue 7090. -/
theorem bounds_15_7090 : exactInterval 15 7090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7090 : oddCount 7090 15 = 7 ∧ acceleratedOrbit 15 7090 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7090) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7090.1, data_15_7090.2]

/-- Complete interval computation for depth 15, residue 7091. -/
theorem bounds_15_7091 : exactInterval 15 7091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7091 : oddCount 7091 15 = 7 ∧ acceleratedOrbit 15 7091 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7091) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7091.1, data_15_7091.2]

/-- Complete interval computation for depth 15, residue 7092. -/
theorem bounds_15_7092 : exactInterval 15 7092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7092 : oddCount 7092 15 = 7 ∧ acceleratedOrbit 15 7092 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7092) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7092.1, data_15_7092.2]

/-- Complete interval computation for depth 15, residue 7093. -/
theorem bounds_15_7093 : exactInterval 15 7093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7093 : oddCount 7093 15 = 7 ∧ acceleratedOrbit 15 7093 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7093) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7093.1, data_15_7093.2]

/-- Complete interval computation for depth 15, residue 7094. -/
theorem bounds_15_7094 : exactInterval 15 7094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7094 : oddCount 7094 15 = 6 ∧ acceleratedOrbit 15 7094 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7094) = 3 ^ 6 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7094.1, data_15_7094.2]

/-- Complete interval computation for depth 15, residue 7095. -/
theorem bounds_15_7095 : exactInterval 15 7095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7095 : oddCount 7095 15 = 6 ∧ acceleratedOrbit 15 7095 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7095) = 3 ^ 6 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7095.1, data_15_7095.2]

/-- Complete interval computation for depth 15, residue 7096. -/
theorem bounds_15_7096 : exactInterval 15 7096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7096 : oddCount 7096 15 = 7 ∧ acceleratedOrbit 15 7096 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7096) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7096.1, data_15_7096.2]

/-- Complete interval computation for depth 15, residue 7097. -/
theorem bounds_15_7097 : exactInterval 15 7097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7097 : oddCount 7097 15 = 6 ∧ acceleratedOrbit 15 7097 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7097) = 3 ^ 6 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7097.1, data_15_7097.2]

/-- Complete interval computation for depth 15, residue 7098. -/
theorem bounds_15_7098 : exactInterval 15 7098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7098 : oddCount 7098 15 = 7 ∧ acceleratedOrbit 15 7098 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7098) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7098.1, data_15_7098.2]

/-- Complete interval computation for depth 15, residue 7099. -/
theorem bounds_15_7099 : exactInterval 15 7099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7099 : oddCount 7099 15 = 6 ∧ acceleratedOrbit 15 7099 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7099) = 3 ^ 6 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7099.1, data_15_7099.2]

/-- Complete interval computation for depth 15, residue 7100. -/
theorem bounds_15_7100 : exactInterval 15 7100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7100 : oddCount 7100 15 = 9 ∧ acceleratedOrbit 15 7100 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7100) = 3 ^ 9 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7100.1, data_15_7100.2]

/-- Complete interval computation for depth 15, residue 7101. -/
theorem bounds_15_7101 : exactInterval 15 7101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7101 : oddCount 7101 15 = 9 ∧ acceleratedOrbit 15 7101 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7101) = 3 ^ 9 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7101.1, data_15_7101.2]

/-- Complete interval computation for depth 15, residue 7102. -/
theorem bounds_15_7102 : exactInterval 15 7102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7102 : oddCount 7102 15 = 9 ∧ acceleratedOrbit 15 7102 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7102) = 3 ^ 9 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7102.1, data_15_7102.2]

/-- Complete interval computation for depth 15, residue 7103. -/
theorem bounds_15_7103 : exactInterval 15 7103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7103 : oddCount 7103 15 = 10 ∧ acceleratedOrbit 15 7103 = 12802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7103) = 3 ^ 10 * m + 12802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7103.1, data_15_7103.2]

/-- Complete interval computation for depth 15, residue 7104. -/
theorem bounds_15_7104 : exactInterval 15 7104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7104 : oddCount 7104 15 = 7 ∧ acceleratedOrbit 15 7104 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7104) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7104.1, data_15_7104.2]

/-- Complete interval computation for depth 15, residue 7105. -/
theorem bounds_15_7105 : exactInterval 15 7105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7105 : oddCount 7105 15 = 8 ∧ acceleratedOrbit 15 7105 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7105) = 3 ^ 8 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7105.1, data_15_7105.2]

/-- Complete interval computation for depth 15, residue 7106. -/
theorem bounds_15_7106 : exactInterval 15 7106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7106 : oddCount 7106 15 = 8 ∧ acceleratedOrbit 15 7106 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7106) = 3 ^ 8 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7106.1, data_15_7106.2]

/-- Complete interval computation for depth 15, residue 7107. -/
theorem bounds_15_7107 : exactInterval 15 7107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7107 : oddCount 7107 15 = 8 ∧ acceleratedOrbit 15 7107 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7107) = 3 ^ 8 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7107.1, data_15_7107.2]

/-- Complete interval computation for depth 15, residue 7108. -/
theorem bounds_15_7108 : exactInterval 15 7108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7108 : oddCount 7108 15 = 6 ∧ acceleratedOrbit 15 7108 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7108) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7108.1, data_15_7108.2]

/-- Complete interval computation for depth 15, residue 7109. -/
theorem bounds_15_7109 : exactInterval 15 7109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7109 : oddCount 7109 15 = 6 ∧ acceleratedOrbit 15 7109 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7109) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7109.1, data_15_7109.2]

end Collatz.Research.PassageAtlas.Batch0217
