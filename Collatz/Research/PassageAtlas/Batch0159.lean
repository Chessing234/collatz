import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0159

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5177. -/
theorem bounds_15_5177 : exactInterval 15 5177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5177 : oddCount 5177 15 = 7 ∧ acceleratedOrbit 15 5177 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5177) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5177.1, data_15_5177.2]

/-- Complete interval computation for depth 15, residue 5178. -/
theorem bounds_15_5178 : exactInterval 15 5178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5178 : oddCount 5178 15 = 6 ∧ acceleratedOrbit 15 5178 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5178) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5178.1, data_15_5178.2]

/-- Complete interval computation for depth 15, residue 5179. -/
theorem bounds_15_5179 : exactInterval 15 5179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5179 : oddCount 5179 15 = 10 ∧ acceleratedOrbit 15 5179 = 9341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5179) = 3 ^ 10 * m + 9341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5179.1, data_15_5179.2]

/-- Complete interval computation for depth 15, residue 5180. -/
theorem bounds_15_5180 : exactInterval 15 5180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5180 : oddCount 5180 15 = 6 ∧ acceleratedOrbit 15 5180 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5180) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5180.1, data_15_5180.2]

/-- Complete interval computation for depth 15, residue 5181. -/
theorem bounds_15_5181 : exactInterval 15 5181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5181 : oddCount 5181 15 = 6 ∧ acceleratedOrbit 15 5181 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5181) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5181.1, data_15_5181.2]

/-- Complete interval computation for depth 15, residue 5182. -/
theorem bounds_15_5182 : exactInterval 15 5182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5182 : oddCount 5182 15 = 7 ∧ acceleratedOrbit 15 5182 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5182) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5182.1, data_15_5182.2]

/-- Complete interval computation for depth 15, residue 5183. -/
theorem bounds_15_5183 : exactInterval 15 5183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5183 : oddCount 5183 15 = 7 ∧ acceleratedOrbit 15 5183 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5183) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5183.1, data_15_5183.2]

/-- Complete interval computation for depth 15, residue 5184. -/
theorem bounds_15_5184 : exactInterval 15 5184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5184 : oddCount 5184 15 = 5 ∧ acceleratedOrbit 15 5184 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5184) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5184.1, data_15_5184.2]

/-- Complete interval computation for depth 15, residue 5185. -/
theorem bounds_15_5185 : exactInterval 15 5185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5185 : oddCount 5185 15 = 6 ∧ acceleratedOrbit 15 5185 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5185) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5185.1, data_15_5185.2]

/-- Complete interval computation for depth 15, residue 5186. -/
theorem bounds_15_5186 : exactInterval 15 5186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5186 : oddCount 5186 15 = 6 ∧ acceleratedOrbit 15 5186 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5186) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5186.1, data_15_5186.2]

/-- Complete interval computation for depth 15, residue 5187. -/
theorem bounds_15_5187 : exactInterval 15 5187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5187 : oddCount 5187 15 = 6 ∧ acceleratedOrbit 15 5187 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5187) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5187.1, data_15_5187.2]

/-- Complete interval computation for depth 15, residue 5188. -/
theorem bounds_15_5188 : exactInterval 15 5188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5188 : oddCount 5188 15 = 7 ∧ acceleratedOrbit 15 5188 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5188) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5188.1, data_15_5188.2]

/-- Complete interval computation for depth 15, residue 5189. -/
theorem bounds_15_5189 : exactInterval 15 5189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5189 : oddCount 5189 15 = 7 ∧ acceleratedOrbit 15 5189 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5189) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5189.1, data_15_5189.2]

/-- Complete interval computation for depth 15, residue 5190. -/
theorem bounds_15_5190 : exactInterval 15 5190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5190 : oddCount 5190 15 = 7 ∧ acceleratedOrbit 15 5190 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5190) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5190.1, data_15_5190.2]

/-- Complete interval computation for depth 15, residue 5191. -/
theorem bounds_15_5191 : exactInterval 15 5191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5191 : oddCount 5191 15 = 10 ∧ acceleratedOrbit 15 5191 = 9359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5191) = 3 ^ 10 * m + 9359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5191.1, data_15_5191.2]

/-- Complete interval computation for depth 15, residue 5192. -/
theorem bounds_15_5192 : exactInterval 15 5192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5192 : oddCount 5192 15 = 8 ∧ acceleratedOrbit 15 5192 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5192) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5192.1, data_15_5192.2]

/-- Complete interval computation for depth 15, residue 5193. -/
theorem bounds_15_5193 : exactInterval 15 5193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5193 : oddCount 5193 15 = 9 ∧ acceleratedOrbit 15 5193 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5193) = 3 ^ 9 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5193.1, data_15_5193.2]

/-- Complete interval computation for depth 15, residue 5194. -/
theorem bounds_15_5194 : exactInterval 15 5194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5194 : oddCount 5194 15 = 8 ∧ acceleratedOrbit 15 5194 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5194) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5194.1, data_15_5194.2]

/-- Complete interval computation for depth 15, residue 5195. -/
theorem bounds_15_5195 : exactInterval 15 5195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5195 : oddCount 5195 15 = 7 ∧ acceleratedOrbit 15 5195 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5195) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5195.1, data_15_5195.2]

/-- Complete interval computation for depth 15, residue 5196. -/
theorem bounds_15_5196 : exactInterval 15 5196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5196 : oddCount 5196 15 = 8 ∧ acceleratedOrbit 15 5196 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5196) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5196.1, data_15_5196.2]

/-- Complete interval computation for depth 15, residue 5197. -/
theorem bounds_15_5197 : exactInterval 15 5197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5197 : oddCount 5197 15 = 8 ∧ acceleratedOrbit 15 5197 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5197) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5197.1, data_15_5197.2]

/-- Complete interval computation for depth 15, residue 5198. -/
theorem bounds_15_5198 : exactInterval 15 5198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5198 : oddCount 5198 15 = 8 ∧ acceleratedOrbit 15 5198 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5198) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5198.1, data_15_5198.2]

/-- Complete interval computation for depth 15, residue 5199. -/
theorem bounds_15_5199 : exactInterval 15 5199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5199 : oddCount 5199 15 = 8 ∧ acceleratedOrbit 15 5199 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5199) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5199.1, data_15_5199.2]

/-- Complete interval computation for depth 15, residue 5200. -/
theorem bounds_15_5200 : exactInterval 15 5200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5200 : oddCount 5200 15 = 5 ∧ acceleratedOrbit 15 5200 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5200) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5200.1, data_15_5200.2]

/-- Complete interval computation for depth 15, residue 5201. -/
theorem bounds_15_5201 : exactInterval 15 5201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5201 : oddCount 5201 15 = 8 ∧ acceleratedOrbit 15 5201 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5201) = 3 ^ 8 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5201.1, data_15_5201.2]

/-- Complete interval computation for depth 15, residue 5202. -/
theorem bounds_15_5202 : exactInterval 15 5202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5202 : oddCount 5202 15 = 9 ∧ acceleratedOrbit 15 5202 = 3127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5202) = 3 ^ 9 * m + 3127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5202.1, data_15_5202.2]

/-- Complete interval computation for depth 15, residue 5203. -/
theorem bounds_15_5203 : exactInterval 15 5203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5203 : oddCount 5203 15 = 9 ∧ acceleratedOrbit 15 5203 = 3127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5203) = 3 ^ 9 * m + 3127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5203.1, data_15_5203.2]

/-- Complete interval computation for depth 15, residue 5204. -/
theorem bounds_15_5204 : exactInterval 15 5204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5204 : oddCount 5204 15 = 5 ∧ acceleratedOrbit 15 5204 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5204) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5204.1, data_15_5204.2]

/-- Complete interval computation for depth 15, residue 5205. -/
theorem bounds_15_5205 : exactInterval 15 5205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5205 : oddCount 5205 15 = 5 ∧ acceleratedOrbit 15 5205 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5205) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5205.1, data_15_5205.2]

/-- Complete interval computation for depth 15, residue 5206. -/
theorem bounds_15_5206 : exactInterval 15 5206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5206 : oddCount 5206 15 = 7 ∧ acceleratedOrbit 15 5206 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5206) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5206.1, data_15_5206.2]

/-- Complete interval computation for depth 15, residue 5207. -/
theorem bounds_15_5207 : exactInterval 15 5207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5207 : oddCount 5207 15 = 7 ∧ acceleratedOrbit 15 5207 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5207) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5207.1, data_15_5207.2]

/-- Complete interval computation for depth 15, residue 5208. -/
theorem bounds_15_5208 : exactInterval 15 5208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5208 : oddCount 5208 15 = 7 ∧ acceleratedOrbit 15 5208 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5208) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5208.1, data_15_5208.2]

/-- Complete interval computation for depth 15, residue 5209. -/
theorem bounds_15_5209 : exactInterval 15 5209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5209 : oddCount 5209 15 = 6 ∧ acceleratedOrbit 15 5209 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5209) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5209.1, data_15_5209.2]

end Collatz.Research.PassageAtlas.Batch0159
