import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0805

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5181. -/
theorem bounds_13_5181 : exactInterval 13 5181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5181 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5181) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5181 : oddCount 5181 13 = 5 ∧ acceleratedOrbit 13 5181 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5181 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5181) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5181.1, data_13_5181.2]

/-- Complete interval computation for depth 13, residue 5182. -/
theorem bounds_13_5182 : exactInterval 13 5182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5182 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5182) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5182 : oddCount 5182 13 = 7 ∧ acceleratedOrbit 13 5182 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5182 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5182) = 3 ^ 7 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5182.1, data_13_5182.2]

/-- Complete interval computation for depth 13, residue 5183. -/
theorem bounds_13_5183 : exactInterval 13 5183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5183 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5183) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5183 : oddCount 5183 13 = 7 ∧ acceleratedOrbit 13 5183 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5183 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5183) = 3 ^ 7 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5183.1, data_13_5183.2]

/-- Complete interval computation for depth 13, residue 5184. -/
theorem bounds_13_5184 : exactInterval 13 5184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5184 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5184) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5184 : oddCount 5184 13 = 4 ∧ acceleratedOrbit 13 5184 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5184 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5184) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5184.1, data_13_5184.2]

/-- Complete interval computation for depth 13, residue 5185. -/
theorem bounds_13_5185 : exactInterval 13 5185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5185 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5185) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5185 : oddCount 5185 13 = 5 ∧ acceleratedOrbit 13 5185 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5185 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5185) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5185.1, data_13_5185.2]

/-- Complete interval computation for depth 13, residue 5186. -/
theorem bounds_13_5186 : exactInterval 13 5186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5186 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5186) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5186 : oddCount 5186 13 = 5 ∧ acceleratedOrbit 13 5186 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5186 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5186) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5186.1, data_13_5186.2]

/-- Complete interval computation for depth 13, residue 5187. -/
theorem bounds_13_5187 : exactInterval 13 5187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5187 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5187) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5187 : oddCount 5187 13 = 5 ∧ acceleratedOrbit 13 5187 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5187 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5187) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5187.1, data_13_5187.2]

/-- Complete interval computation for depth 13, residue 5188. -/
theorem bounds_13_5188 : exactInterval 13 5188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5188 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5188) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5188 : oddCount 5188 13 = 5 ∧ acceleratedOrbit 13 5188 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5188 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5188) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5188.1, data_13_5188.2]

/-- Complete interval computation for depth 13, residue 5189. -/
theorem bounds_13_5189 : exactInterval 13 5189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5189 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5189) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5189 : oddCount 5189 13 = 5 ∧ acceleratedOrbit 13 5189 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5189 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5189) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5189.1, data_13_5189.2]

/-- Complete interval computation for depth 13, residue 5190. -/
theorem bounds_13_5190 : exactInterval 13 5190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5190 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5190) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5190 : oddCount 5190 13 = 5 ∧ acceleratedOrbit 13 5190 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5190 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5190) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5190.1, data_13_5190.2]

/-- Complete interval computation for depth 13, residue 5191. -/
theorem bounds_13_5191 : exactInterval 13 5191 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5191 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5191) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5191 : oddCount 5191 13 = 8 ∧ acceleratedOrbit 13 5191 = 4159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5191 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5191) = 3 ^ 8 * m + 4159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5191.1, data_13_5191.2]

/-- Complete interval computation for depth 13, residue 5192. -/
theorem bounds_13_5192 : exactInterval 13 5192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5192 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5192) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5192 : oddCount 5192 13 = 7 ∧ acceleratedOrbit 13 5192 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5192 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5192) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5192.1, data_13_5192.2]

/-- Complete interval computation for depth 13, residue 5193. -/
theorem bounds_13_5193 : exactInterval 13 5193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5193 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5193) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5193 : oddCount 5193 13 = 7 ∧ acceleratedOrbit 13 5193 = 1387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5193 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5193) = 3 ^ 7 * m + 1387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5193.1, data_13_5193.2]

/-- Complete interval computation for depth 13, residue 5194. -/
theorem bounds_13_5194 : exactInterval 13 5194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5194 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5194) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5194 : oddCount 5194 13 = 7 ∧ acceleratedOrbit 13 5194 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5194 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5194) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5194.1, data_13_5194.2]

/-- Complete interval computation for depth 13, residue 5195. -/
theorem bounds_13_5195 : exactInterval 13 5195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5195 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5195) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5195 : oddCount 5195 13 = 5 ∧ acceleratedOrbit 13 5195 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5195 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5195) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5195.1, data_13_5195.2]

end Collatz.Research.StoppingAtlas.Batch0805
