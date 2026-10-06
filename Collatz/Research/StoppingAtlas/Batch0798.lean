import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0798

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5073. -/
theorem bounds_13_5073 : exactInterval 13 5073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5073 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5073) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5073 : oddCount 5073 13 = 6 ∧ acceleratedOrbit 13 5073 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5073 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5073) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5073.1, data_13_5073.2]

/-- Complete interval computation for depth 13, residue 5074. -/
theorem bounds_13_5074 : exactInterval 13 5074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5074 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5074) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5074 : oddCount 5074 13 = 8 ∧ acceleratedOrbit 13 5074 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5074 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5074) = 3 ^ 8 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5074.1, data_13_5074.2]

/-- Complete interval computation for depth 13, residue 5075. -/
theorem bounds_13_5075 : exactInterval 13 5075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5075 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5075) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5075 : oddCount 5075 13 = 8 ∧ acceleratedOrbit 13 5075 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5075 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5075) = 3 ^ 8 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5075.1, data_13_5075.2]

/-- Complete interval computation for depth 13, residue 5076. -/
theorem bounds_13_5076 : exactInterval 13 5076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5076 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5076) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5076 : oddCount 5076 13 = 5 ∧ acceleratedOrbit 13 5076 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5076 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5076) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5076.1, data_13_5076.2]

/-- Complete interval computation for depth 13, residue 5077. -/
theorem bounds_13_5077 : exactInterval 13 5077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5077 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5077) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5077 : oddCount 5077 13 = 5 ∧ acceleratedOrbit 13 5077 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5077 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5077) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5077.1, data_13_5077.2]

/-- Complete interval computation for depth 13, residue 5078. -/
theorem bounds_13_5078 : exactInterval 13 5078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5078 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5078) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5078 : oddCount 5078 13 = 8 ∧ acceleratedOrbit 13 5078 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5078 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5078) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5078.1, data_13_5078.2]

/-- Complete interval computation for depth 13, residue 5079. -/
theorem bounds_13_5079 : exactInterval 13 5079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5079 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5079) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5079 : oddCount 5079 13 = 8 ∧ acceleratedOrbit 13 5079 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5079 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5079) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5079.1, data_13_5079.2]

/-- Complete interval computation for depth 13, residue 5080. -/
theorem bounds_13_5080 : exactInterval 13 5080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5080 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5080) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5080 : oddCount 5080 13 = 5 ∧ acceleratedOrbit 13 5080 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5080 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5080) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5080.1, data_13_5080.2]

/-- Complete interval computation for depth 13, residue 5081. -/
theorem bounds_13_5081 : exactInterval 13 5081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5081 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5081) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5081 : oddCount 5081 13 = 5 ∧ acceleratedOrbit 13 5081 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5081 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5081) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5081.1, data_13_5081.2]

/-- Complete interval computation for depth 13, residue 5082. -/
theorem bounds_13_5082 : exactInterval 13 5082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5082 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5082) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5082 : oddCount 5082 13 = 5 ∧ acceleratedOrbit 13 5082 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5082 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5082) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5082.1, data_13_5082.2]

/-- Complete interval computation for depth 13, residue 5083. -/
theorem bounds_13_5083 : exactInterval 13 5083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5083 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5083) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5083 : oddCount 5083 13 = 7 ∧ acceleratedOrbit 13 5083 = 1358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5083 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5083) = 3 ^ 7 * m + 1358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5083.1, data_13_5083.2]

/-- Complete interval computation for depth 13, residue 5084. -/
theorem bounds_13_5084 : exactInterval 13 5084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5084 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5084) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5084 : oddCount 5084 13 = 5 ∧ acceleratedOrbit 13 5084 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5084 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5084) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5084.1, data_13_5084.2]

/-- Complete interval computation for depth 13, residue 5085. -/
theorem bounds_13_5085 : exactInterval 13 5085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5085 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5085) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5085 : oddCount 5085 13 = 5 ∧ acceleratedOrbit 13 5085 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5085 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5085) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5085.1, data_13_5085.2]

/-- Complete interval computation for depth 13, residue 5086. -/
theorem bounds_13_5086 : exactInterval 13 5086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5086 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5086) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5086 : oddCount 5086 13 = 9 ∧ acceleratedOrbit 13 5086 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5086 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5086) = 3 ^ 9 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5086.1, data_13_5086.2]

/-- Complete interval computation for depth 13, residue 5087. -/
theorem bounds_13_5087 : exactInterval 13 5087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5087 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5087) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5087 : oddCount 5087 13 = 9 ∧ acceleratedOrbit 13 5087 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5087 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5087) = 3 ^ 9 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5087.1, data_13_5087.2]

/-- Complete interval computation for depth 13, residue 5088. -/
theorem bounds_13_5088 : exactInterval 13 5088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5088 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5088) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5088 : oddCount 5088 13 = 7 ∧ acceleratedOrbit 13 5088 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5088 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5088) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5088.1, data_13_5088.2]

end Collatz.Research.StoppingAtlas.Batch0798
