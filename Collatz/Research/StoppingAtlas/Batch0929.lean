import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0929

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7086. -/
theorem bounds_13_7086 : exactInterval 13 7086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7086 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7086) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7086 : oddCount 7086 13 = 6 ∧ acceleratedOrbit 13 7086 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7086 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7086) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7086.1, data_13_7086.2]

/-- Complete interval computation for depth 13, residue 7087. -/
theorem bounds_13_7087 : exactInterval 13 7087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7087 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7087) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7087 : oddCount 7087 13 = 6 ∧ acceleratedOrbit 13 7087 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7087 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7087) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7087.1, data_13_7087.2]

/-- Complete interval computation for depth 13, residue 7088. -/
theorem bounds_13_7088 : exactInterval 13 7088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7088 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7088) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7088 : oddCount 7088 13 = 5 ∧ acceleratedOrbit 13 7088 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7088 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7088) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7088.1, data_13_7088.2]

/-- Complete interval computation for depth 13, residue 7089. -/
theorem bounds_13_7089 : exactInterval 13 7089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7089 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7089) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7089 : oddCount 7089 13 = 5 ∧ acceleratedOrbit 13 7089 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7089 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7089) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7089.1, data_13_7089.2]

/-- Complete interval computation for depth 13, residue 7090. -/
theorem bounds_13_7090 : exactInterval 13 7090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7090 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7090) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7090 : oddCount 7090 13 = 5 ∧ acceleratedOrbit 13 7090 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7090 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7090) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7090.1, data_13_7090.2]

/-- Complete interval computation for depth 13, residue 7091. -/
theorem bounds_13_7091 : exactInterval 13 7091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7091 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7091) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7091 : oddCount 7091 13 = 5 ∧ acceleratedOrbit 13 7091 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7091 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7091) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7091.1, data_13_7091.2]

/-- Complete interval computation for depth 13, residue 7092. -/
theorem bounds_13_7092 : exactInterval 13 7092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7092 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7092) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7092 : oddCount 7092 13 = 5 ∧ acceleratedOrbit 13 7092 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7092 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7092) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7092.1, data_13_7092.2]

/-- Complete interval computation for depth 13, residue 7093. -/
theorem bounds_13_7093 : exactInterval 13 7093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7093 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7093) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7093 : oddCount 7093 13 = 5 ∧ acceleratedOrbit 13 7093 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7093 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7093) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7093.1, data_13_7093.2]

/-- Complete interval computation for depth 13, residue 7094. -/
theorem bounds_13_7094 : exactInterval 13 7094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7094 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7094) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7094 : oddCount 7094 13 = 6 ∧ acceleratedOrbit 13 7094 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7094 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7094) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7094.1, data_13_7094.2]

/-- Complete interval computation for depth 13, residue 7095. -/
theorem bounds_13_7095 : exactInterval 13 7095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7095 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7095) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7095 : oddCount 7095 13 = 6 ∧ acceleratedOrbit 13 7095 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7095 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7095) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7095.1, data_13_7095.2]

/-- Complete interval computation for depth 13, residue 7096. -/
theorem bounds_13_7096 : exactInterval 13 7096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7096 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7096) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7096 : oddCount 7096 13 = 5 ∧ acceleratedOrbit 13 7096 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7096 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7096) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7096.1, data_13_7096.2]

/-- Complete interval computation for depth 13, residue 7097. -/
theorem bounds_13_7097 : exactInterval 13 7097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7097 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7097) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7097 : oddCount 7097 13 = 6 ∧ acceleratedOrbit 13 7097 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7097 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7097) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7097.1, data_13_7097.2]

/-- Complete interval computation for depth 13, residue 7098. -/
theorem bounds_13_7098 : exactInterval 13 7098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7098 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7098) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7098 : oddCount 7098 13 = 5 ∧ acceleratedOrbit 13 7098 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7098 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7098) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7098.1, data_13_7098.2]

/-- Complete interval computation for depth 13, residue 7099. -/
theorem bounds_13_7099 : exactInterval 13 7099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7099 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7099) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7099 : oddCount 7099 13 = 6 ∧ acceleratedOrbit 13 7099 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7099 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7099) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7099.1, data_13_7099.2]

/-- Complete interval computation for depth 13, residue 7100. -/
theorem bounds_13_7100 : exactInterval 13 7100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7100 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7100) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7100 : oddCount 7100 13 = 8 ∧ acceleratedOrbit 13 7100 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7100 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7100) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7100.1, data_13_7100.2]

end Collatz.Research.StoppingAtlas.Batch0929
