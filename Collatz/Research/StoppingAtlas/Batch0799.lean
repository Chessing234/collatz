import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0799

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5089. -/
theorem bounds_13_5089 : exactInterval 13 5089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5089 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5089) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5089 : oddCount 5089 13 = 8 ∧ acceleratedOrbit 13 5089 = 4078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5089 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5089) = 3 ^ 8 * m + 4078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5089.1, data_13_5089.2]

/-- Complete interval computation for depth 13, residue 5090. -/
theorem bounds_13_5090 : exactInterval 13 5090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5090 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5090) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5090 : oddCount 5090 13 = 5 ∧ acceleratedOrbit 13 5090 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5090 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5090) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5090.1, data_13_5090.2]

/-- Complete interval computation for depth 13, residue 5091. -/
theorem bounds_13_5091 : exactInterval 13 5091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5091 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5091) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5091 : oddCount 5091 13 = 5 ∧ acceleratedOrbit 13 5091 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5091 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5091) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5091.1, data_13_5091.2]

/-- Complete interval computation for depth 13, residue 5092. -/
theorem bounds_13_5092 : exactInterval 13 5092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5092 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5092) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5092 : oddCount 5092 13 = 6 ∧ acceleratedOrbit 13 5092 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5092 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5092) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5092.1, data_13_5092.2]

/-- Complete interval computation for depth 13, residue 5093. -/
theorem bounds_13_5093 : exactInterval 13 5093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5093 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5093) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5093 : oddCount 5093 13 = 6 ∧ acceleratedOrbit 13 5093 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5093 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5093) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5093.1, data_13_5093.2]

/-- Complete interval computation for depth 13, residue 5094. -/
theorem bounds_13_5094 : exactInterval 13 5094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5094 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5094) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5094 : oddCount 5094 13 = 6 ∧ acceleratedOrbit 13 5094 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5094 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5094) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5094.1, data_13_5094.2]

/-- Complete interval computation for depth 13, residue 5095. -/
theorem bounds_13_5095 : exactInterval 13 5095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5095 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5095) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5095 : oddCount 5095 13 = 7 ∧ acceleratedOrbit 13 5095 = 1361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5095 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5095) = 3 ^ 7 * m + 1361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5095.1, data_13_5095.2]

/-- Complete interval computation for depth 13, residue 5096. -/
theorem bounds_13_5096 : exactInterval 13 5096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5096 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5096) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5096 : oddCount 5096 13 = 7 ∧ acceleratedOrbit 13 5096 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5096 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5096) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5096.1, data_13_5096.2]

/-- Complete interval computation for depth 13, residue 5097. -/
theorem bounds_13_5097 : exactInterval 13 5097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5097 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5097) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5097 : oddCount 5097 13 = 9 ∧ acceleratedOrbit 13 5097 = 12251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5097 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5097) = 3 ^ 9 * m + 12251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5097.1, data_13_5097.2]

/-- Complete interval computation for depth 13, residue 5098. -/
theorem bounds_13_5098 : exactInterval 13 5098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5098 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5098) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5098 : oddCount 5098 13 = 7 ∧ acceleratedOrbit 13 5098 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5098 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5098) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5098.1, data_13_5098.2]

/-- Complete interval computation for depth 13, residue 5099. -/
theorem bounds_13_5099 : exactInterval 13 5099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5099 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5099) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5099 : oddCount 5099 13 = 9 ∧ acceleratedOrbit 13 5099 = 12257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5099 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5099) = 3 ^ 9 * m + 12257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5099.1, data_13_5099.2]

/-- Complete interval computation for depth 13, residue 5100. -/
theorem bounds_13_5100 : exactInterval 13 5100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5100 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5100) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5100 : oddCount 5100 13 = 8 ∧ acceleratedOrbit 13 5100 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5100 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5100) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5100.1, data_13_5100.2]

/-- Complete interval computation for depth 13, residue 5101. -/
theorem bounds_13_5101 : exactInterval 13 5101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5101 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5101) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5101 : oddCount 5101 13 = 8 ∧ acceleratedOrbit 13 5101 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5101 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5101) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5101.1, data_13_5101.2]

/-- Complete interval computation for depth 13, residue 5102. -/
theorem bounds_13_5102 : exactInterval 13 5102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5102 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5102) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5102 : oddCount 5102 13 = 8 ∧ acceleratedOrbit 13 5102 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5102 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5102) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5102.1, data_13_5102.2]

/-- Complete interval computation for depth 13, residue 5103. -/
theorem bounds_13_5103 : exactInterval 13 5103 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5103 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5103) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5103 : oddCount 5103 13 = 8 ∧ acceleratedOrbit 13 5103 = 4088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5103 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5103) = 3 ^ 8 * m + 4088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5103.1, data_13_5103.2]

end Collatz.Research.StoppingAtlas.Batch0799
