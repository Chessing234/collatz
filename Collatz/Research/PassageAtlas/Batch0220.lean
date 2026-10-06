import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0220

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7176. -/
theorem bounds_15_7176 : exactInterval 15 7176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7176 : oddCount 7176 15 = 7 ∧ acceleratedOrbit 15 7176 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7176) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7176.1, data_15_7176.2]

/-- Complete interval computation for depth 15, residue 7177. -/
theorem bounds_15_7177 : exactInterval 15 7177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7177 : oddCount 7177 15 = 9 ∧ acceleratedOrbit 15 7177 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7177) = 3 ^ 9 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7177.1, data_15_7177.2]

/-- Complete interval computation for depth 15, residue 7178. -/
theorem bounds_15_7178 : exactInterval 15 7178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7178 : oddCount 7178 15 = 7 ∧ acceleratedOrbit 15 7178 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7178) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7178.1, data_15_7178.2]

/-- Complete interval computation for depth 15, residue 7179. -/
theorem bounds_15_7179 : exactInterval 15 7179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7179 : oddCount 7179 15 = 6 ∧ acceleratedOrbit 15 7179 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7179) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7179.1, data_15_7179.2]

/-- Complete interval computation for depth 15, residue 7180. -/
theorem bounds_15_7180 : exactInterval 15 7180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7180 : oddCount 7180 15 = 7 ∧ acceleratedOrbit 15 7180 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7180) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7180.1, data_15_7180.2]

/-- Complete interval computation for depth 15, residue 7181. -/
theorem bounds_15_7181 : exactInterval 15 7181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7181 : oddCount 7181 15 = 7 ∧ acceleratedOrbit 15 7181 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7181) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7181.1, data_15_7181.2]

/-- Complete interval computation for depth 15, residue 7182. -/
theorem bounds_15_7182 : exactInterval 15 7182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7182 : oddCount 7182 15 = 9 ∧ acceleratedOrbit 15 7182 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7182) = 3 ^ 9 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7182.1, data_15_7182.2]

/-- Complete interval computation for depth 15, residue 7183. -/
theorem bounds_15_7183 : exactInterval 15 7183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7183 : oddCount 7183 15 = 9 ∧ acceleratedOrbit 15 7183 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7183) = 3 ^ 9 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7183.1, data_15_7183.2]

/-- Complete interval computation for depth 15, residue 7184. -/
theorem bounds_15_7184 : exactInterval 15 7184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7184 : oddCount 7184 15 = 7 ∧ acceleratedOrbit 15 7184 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7184) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7184.1, data_15_7184.2]

/-- Complete interval computation for depth 15, residue 7185. -/
theorem bounds_15_7185 : exactInterval 15 7185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7185 : oddCount 7185 15 = 7 ∧ acceleratedOrbit 15 7185 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7185) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7185.1, data_15_7185.2]

/-- Complete interval computation for depth 15, residue 7186. -/
theorem bounds_15_7186 : exactInterval 15 7186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7186 : oddCount 7186 15 = 6 ∧ acceleratedOrbit 15 7186 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7186) = 3 ^ 6 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7186.1, data_15_7186.2]

/-- Complete interval computation for depth 15, residue 7187. -/
theorem bounds_15_7187 : exactInterval 15 7187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7187 : oddCount 7187 15 = 6 ∧ acceleratedOrbit 15 7187 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7187) = 3 ^ 6 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7187.1, data_15_7187.2]

/-- Complete interval computation for depth 15, residue 7188. -/
theorem bounds_15_7188 : exactInterval 15 7188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7188 : oddCount 7188 15 = 7 ∧ acceleratedOrbit 15 7188 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7188) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7188.1, data_15_7188.2]

/-- Complete interval computation for depth 15, residue 7189. -/
theorem bounds_15_7189 : exactInterval 15 7189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7189 : oddCount 7189 15 = 7 ∧ acceleratedOrbit 15 7189 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7189) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7189.1, data_15_7189.2]

/-- Complete interval computation for depth 15, residue 7190. -/
theorem bounds_15_7190 : exactInterval 15 7190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7190 : oddCount 7190 15 = 7 ∧ acceleratedOrbit 15 7190 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7190) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7190.1, data_15_7190.2]

/-- Complete interval computation for depth 15, residue 7191. -/
theorem bounds_15_7191 : exactInterval 15 7191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7191 : oddCount 7191 15 = 7 ∧ acceleratedOrbit 15 7191 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7191) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7191.1, data_15_7191.2]

/-- Complete interval computation for depth 15, residue 7192. -/
theorem bounds_15_7192 : exactInterval 15 7192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7192 : oddCount 7192 15 = 7 ∧ acceleratedOrbit 15 7192 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7192) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7192.1, data_15_7192.2]

/-- Complete interval computation for depth 15, residue 7193. -/
theorem bounds_15_7193 : exactInterval 15 7193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7193 : oddCount 7193 15 = 8 ∧ acceleratedOrbit 15 7193 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7193) = 3 ^ 8 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7193.1, data_15_7193.2]

/-- Complete interval computation for depth 15, residue 7194. -/
theorem bounds_15_7194 : exactInterval 15 7194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7194 : oddCount 7194 15 = 7 ∧ acceleratedOrbit 15 7194 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7194) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7194.1, data_15_7194.2]

/-- Complete interval computation for depth 15, residue 7195. -/
theorem bounds_15_7195 : exactInterval 15 7195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7195 : oddCount 7195 15 = 11 ∧ acceleratedOrbit 15 7195 = 38906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7195) = 3 ^ 11 * m + 38906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7195.1, data_15_7195.2]

/-- Complete interval computation for depth 15, residue 7196. -/
theorem bounds_15_7196 : exactInterval 15 7196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7196 : oddCount 7196 15 = 7 ∧ acceleratedOrbit 15 7196 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7196) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7196.1, data_15_7196.2]

/-- Complete interval computation for depth 15, residue 7197. -/
theorem bounds_15_7197 : exactInterval 15 7197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7197 : oddCount 7197 15 = 7 ∧ acceleratedOrbit 15 7197 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7197) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7197.1, data_15_7197.2]

/-- Complete interval computation for depth 15, residue 7198. -/
theorem bounds_15_7198 : exactInterval 15 7198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7198 : oddCount 7198 15 = 7 ∧ acceleratedOrbit 15 7198 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7198) = 3 ^ 7 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7198.1, data_15_7198.2]

/-- Complete interval computation for depth 15, residue 7199. -/
theorem bounds_15_7199 : exactInterval 15 7199 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7199) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7199 : oddCount 7199 15 = 9 ∧ acceleratedOrbit 15 7199 = 4325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7199) = 3 ^ 9 * m + 4325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7199.1, data_15_7199.2]

/-- Complete interval computation for depth 15, residue 7200. -/
theorem bounds_15_7200 : exactInterval 15 7200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7200 : oddCount 7200 15 = 8 ∧ acceleratedOrbit 15 7200 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7200) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7200.1, data_15_7200.2]

/-- Complete interval computation for depth 15, residue 7201. -/
theorem bounds_15_7201 : exactInterval 15 7201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7201 : oddCount 7201 15 = 10 ∧ acceleratedOrbit 15 7201 = 12986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7201) = 3 ^ 10 * m + 12986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7201.1, data_15_7201.2]

/-- Complete interval computation for depth 15, residue 7202. -/
theorem bounds_15_7202 : exactInterval 15 7202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7202 : oddCount 7202 15 = 7 ∧ acceleratedOrbit 15 7202 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7202) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7202.1, data_15_7202.2]

/-- Complete interval computation for depth 15, residue 7203. -/
theorem bounds_15_7203 : exactInterval 15 7203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7203 : oddCount 7203 15 = 7 ∧ acceleratedOrbit 15 7203 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7203) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7203.1, data_15_7203.2]

/-- Complete interval computation for depth 15, residue 7204. -/
theorem bounds_15_7204 : exactInterval 15 7204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7204 : oddCount 7204 15 = 9 ∧ acceleratedOrbit 15 7204 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7204) = 3 ^ 9 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7204.1, data_15_7204.2]

/-- Complete interval computation for depth 15, residue 7205. -/
theorem bounds_15_7205 : exactInterval 15 7205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7205 : oddCount 7205 15 = 9 ∧ acceleratedOrbit 15 7205 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7205) = 3 ^ 9 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7205.1, data_15_7205.2]

/-- Complete interval computation for depth 15, residue 7206. -/
theorem bounds_15_7206 : exactInterval 15 7206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7206 : oddCount 7206 15 = 9 ∧ acceleratedOrbit 15 7206 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7206) = 3 ^ 9 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7206.1, data_15_7206.2]

/-- Complete interval computation for depth 15, residue 7207. -/
theorem bounds_15_7207 : exactInterval 15 7207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7207 : oddCount 7207 15 = 8 ∧ acceleratedOrbit 15 7207 = 1444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7207) = 3 ^ 8 * m + 1444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7207.1, data_15_7207.2]

end Collatz.Research.PassageAtlas.Batch0220
