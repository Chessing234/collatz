import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0156

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5079. -/
theorem bounds_15_5079 : exactInterval 15 5079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5079 : oddCount 5079 15 = 9 ∧ acceleratedOrbit 15 5079 = 3053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5079) = 3 ^ 9 * m + 3053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5079.1, data_15_5079.2]

/-- Complete interval computation for depth 15, residue 5080. -/
theorem bounds_15_5080 : exactInterval 15 5080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5080 : oddCount 5080 15 = 7 ∧ acceleratedOrbit 15 5080 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5080) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5080.1, data_15_5080.2]

/-- Complete interval computation for depth 15, residue 5081. -/
theorem bounds_15_5081 : exactInterval 15 5081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5081 : oddCount 5081 15 = 5 ∧ acceleratedOrbit 15 5081 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5081) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5081.1, data_15_5081.2]

/-- Complete interval computation for depth 15, residue 5082. -/
theorem bounds_15_5082 : exactInterval 15 5082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5082 : oddCount 5082 15 = 7 ∧ acceleratedOrbit 15 5082 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5082) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5082.1, data_15_5082.2]

/-- Complete interval computation for depth 15, residue 5083. -/
theorem bounds_15_5083 : exactInterval 15 5083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5083 : oddCount 5083 15 = 8 ∧ acceleratedOrbit 15 5083 = 1019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5083) = 3 ^ 8 * m + 1019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5083.1, data_15_5083.2]

/-- Complete interval computation for depth 15, residue 5084. -/
theorem bounds_15_5084 : exactInterval 15 5084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5084 : oddCount 5084 15 = 7 ∧ acceleratedOrbit 15 5084 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5084) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5084.1, data_15_5084.2]

/-- Complete interval computation for depth 15, residue 5085. -/
theorem bounds_15_5085 : exactInterval 15 5085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5085 : oddCount 5085 15 = 7 ∧ acceleratedOrbit 15 5085 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5085) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5085.1, data_15_5085.2]

/-- Complete interval computation for depth 15, residue 5086. -/
theorem bounds_15_5086 : exactInterval 15 5086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5086 : oddCount 5086 15 = 10 ∧ acceleratedOrbit 15 5086 = 9170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5086) = 3 ^ 10 * m + 9170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5086.1, data_15_5086.2]

/-- Complete interval computation for depth 15, residue 5087. -/
theorem bounds_15_5087 : exactInterval 15 5087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5087 : oddCount 5087 15 = 10 ∧ acceleratedOrbit 15 5087 = 9170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5087) = 3 ^ 10 * m + 9170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5087.1, data_15_5087.2]

/-- Complete interval computation for depth 15, residue 5088. -/
theorem bounds_15_5088 : exactInterval 15 5088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5088 : oddCount 5088 15 = 9 ∧ acceleratedOrbit 15 5088 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5088) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5088.1, data_15_5088.2]

/-- Complete interval computation for depth 15, residue 5089. -/
theorem bounds_15_5089 : exactInterval 15 5089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5089 : oddCount 5089 15 = 9 ∧ acceleratedOrbit 15 5089 = 3059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5089) = 3 ^ 9 * m + 3059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5089.1, data_15_5089.2]

/-- Complete interval computation for depth 15, residue 5090. -/
theorem bounds_15_5090 : exactInterval 15 5090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5090 : oddCount 5090 15 = 5 ∧ acceleratedOrbit 15 5090 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5090) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5090.1, data_15_5090.2]

/-- Complete interval computation for depth 15, residue 5091. -/
theorem bounds_15_5091 : exactInterval 15 5091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5091 : oddCount 5091 15 = 5 ∧ acceleratedOrbit 15 5091 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5091) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5091.1, data_15_5091.2]

/-- Complete interval computation for depth 15, residue 5092. -/
theorem bounds_15_5092 : exactInterval 15 5092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5092 : oddCount 5092 15 = 7 ∧ acceleratedOrbit 15 5092 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5092) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5092.1, data_15_5092.2]

/-- Complete interval computation for depth 15, residue 5093. -/
theorem bounds_15_5093 : exactInterval 15 5093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5093 : oddCount 5093 15 = 7 ∧ acceleratedOrbit 15 5093 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5093) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5093.1, data_15_5093.2]

/-- Complete interval computation for depth 15, residue 5094. -/
theorem bounds_15_5094 : exactInterval 15 5094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5094 : oddCount 5094 15 = 7 ∧ acceleratedOrbit 15 5094 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5094) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5094.1, data_15_5094.2]

/-- Complete interval computation for depth 15, residue 5095. -/
theorem bounds_15_5095 : exactInterval 15 5095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5095 : oddCount 5095 15 = 8 ∧ acceleratedOrbit 15 5095 = 1021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5095) = 3 ^ 8 * m + 1021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5095.1, data_15_5095.2]

/-- Complete interval computation for depth 15, residue 5096. -/
theorem bounds_15_5096 : exactInterval 15 5096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5096 : oddCount 5096 15 = 9 ∧ acceleratedOrbit 15 5096 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5096) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5096.1, data_15_5096.2]

/-- Complete interval computation for depth 15, residue 5097. -/
theorem bounds_15_5097 : exactInterval 15 5097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5097 : oddCount 5097 15 = 11 ∧ acceleratedOrbit 15 5097 = 27566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5097) = 3 ^ 11 * m + 27566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5097.1, data_15_5097.2]

/-- Complete interval computation for depth 15, residue 5098. -/
theorem bounds_15_5098 : exactInterval 15 5098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5098 : oddCount 5098 15 = 9 ∧ acceleratedOrbit 15 5098 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5098) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5098.1, data_15_5098.2]

/-- Complete interval computation for depth 15, residue 5099. -/
theorem bounds_15_5099 : exactInterval 15 5099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5099 : oddCount 5099 15 = 10 ∧ acceleratedOrbit 15 5099 = 9193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5099) = 3 ^ 10 * m + 9193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5099.1, data_15_5099.2]

/-- Complete interval computation for depth 15, residue 5100. -/
theorem bounds_15_5100 : exactInterval 15 5100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5100 : oddCount 5100 15 = 9 ∧ acceleratedOrbit 15 5100 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5100) = 3 ^ 9 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5100.1, data_15_5100.2]

/-- Complete interval computation for depth 15, residue 5101. -/
theorem bounds_15_5101 : exactInterval 15 5101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5101 : oddCount 5101 15 = 9 ∧ acceleratedOrbit 15 5101 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5101) = 3 ^ 9 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5101.1, data_15_5101.2]

/-- Complete interval computation for depth 15, residue 5102. -/
theorem bounds_15_5102 : exactInterval 15 5102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5102 : oddCount 5102 15 = 9 ∧ acceleratedOrbit 15 5102 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5102) = 3 ^ 9 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5102.1, data_15_5102.2]

/-- Complete interval computation for depth 15, residue 5103. -/
theorem bounds_15_5103 : exactInterval 15 5103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5103 : oddCount 5103 15 = 8 ∧ acceleratedOrbit 15 5103 = 1022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5103) = 3 ^ 8 * m + 1022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5103.1, data_15_5103.2]

/-- Complete interval computation for depth 15, residue 5104. -/
theorem bounds_15_5104 : exactInterval 15 5104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5104 : oddCount 5104 15 = 9 ∧ acceleratedOrbit 15 5104 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5104) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5104.1, data_15_5104.2]

/-- Complete interval computation for depth 15, residue 5105. -/
theorem bounds_15_5105 : exactInterval 15 5105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5105 : oddCount 5105 15 = 9 ∧ acceleratedOrbit 15 5105 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5105) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5105.1, data_15_5105.2]

/-- Complete interval computation for depth 15, residue 5106. -/
theorem bounds_15_5106 : exactInterval 15 5106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5106 : oddCount 5106 15 = 9 ∧ acceleratedOrbit 15 5106 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5106) = 3 ^ 9 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5106.1, data_15_5106.2]

/-- Complete interval computation for depth 15, residue 5107. -/
theorem bounds_15_5107 : exactInterval 15 5107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5107 : oddCount 5107 15 = 9 ∧ acceleratedOrbit 15 5107 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5107) = 3 ^ 9 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5107.1, data_15_5107.2]

/-- Complete interval computation for depth 15, residue 5108. -/
theorem bounds_15_5108 : exactInterval 15 5108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5108 : oddCount 5108 15 = 9 ∧ acceleratedOrbit 15 5108 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5108) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5108.1, data_15_5108.2]

/-- Complete interval computation for depth 15, residue 5109. -/
theorem bounds_15_5109 : exactInterval 15 5109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5109 : oddCount 5109 15 = 9 ∧ acceleratedOrbit 15 5109 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5109) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5109.1, data_15_5109.2]

/-- Complete interval computation for depth 15, residue 5110. -/
theorem bounds_15_5110 : exactInterval 15 5110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5110 : oddCount 5110 15 = 8 ∧ acceleratedOrbit 15 5110 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5110) = 3 ^ 8 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5110.1, data_15_5110.2]

end Collatz.Research.PassageAtlas.Batch0156
