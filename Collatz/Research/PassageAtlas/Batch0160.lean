import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0160

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5210. -/
theorem bounds_15_5210 : exactInterval 15 5210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5210 : oddCount 5210 15 = 7 ∧ acceleratedOrbit 15 5210 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5210) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5210.1, data_15_5210.2]

/-- Complete interval computation for depth 15, residue 5211. -/
theorem bounds_15_5211 : exactInterval 15 5211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5211 : oddCount 5211 15 = 11 ∧ acceleratedOrbit 15 5211 = 28181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5211) = 3 ^ 11 * m + 28181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5211.1, data_15_5211.2]

/-- Complete interval computation for depth 15, residue 5212. -/
theorem bounds_15_5212 : exactInterval 15 5212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5212 : oddCount 5212 15 = 7 ∧ acceleratedOrbit 15 5212 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5212) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5212.1, data_15_5212.2]

/-- Complete interval computation for depth 15, residue 5213. -/
theorem bounds_15_5213 : exactInterval 15 5213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5213 : oddCount 5213 15 = 7 ∧ acceleratedOrbit 15 5213 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5213) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5213.1, data_15_5213.2]

/-- Complete interval computation for depth 15, residue 5214. -/
theorem bounds_15_5214 : exactInterval 15 5214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5214 : oddCount 5214 15 = 9 ∧ acceleratedOrbit 15 5214 = 3134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5214) = 3 ^ 9 * m + 3134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5214.1, data_15_5214.2]

/-- Complete interval computation for depth 15, residue 5215. -/
theorem bounds_15_5215 : exactInterval 15 5215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5215 : oddCount 5215 15 = 9 ∧ acceleratedOrbit 15 5215 = 3134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5215) = 3 ^ 9 * m + 3134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5215.1, data_15_5215.2]

/-- Complete interval computation for depth 15, residue 5216. -/
theorem bounds_15_5216 : exactInterval 15 5216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5216 : oddCount 5216 15 = 5 ∧ acceleratedOrbit 15 5216 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5216) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5216.1, data_15_5216.2]

/-- Complete interval computation for depth 15, residue 5217. -/
theorem bounds_15_5217 : exactInterval 15 5217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5217 : oddCount 5217 15 = 8 ∧ acceleratedOrbit 15 5217 = 1046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5217) = 3 ^ 8 * m + 1046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5217.1, data_15_5217.2]

/-- Complete interval computation for depth 15, residue 5218. -/
theorem bounds_15_5218 : exactInterval 15 5218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5218 : oddCount 5218 15 = 8 ∧ acceleratedOrbit 15 5218 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5218) = 3 ^ 8 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5218.1, data_15_5218.2]

/-- Complete interval computation for depth 15, residue 5219. -/
theorem bounds_15_5219 : exactInterval 15 5219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5219 : oddCount 5219 15 = 8 ∧ acceleratedOrbit 15 5219 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5219) = 3 ^ 8 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5219.1, data_15_5219.2]

/-- Complete interval computation for depth 15, residue 5220. -/
theorem bounds_15_5220 : exactInterval 15 5220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5220 : oddCount 5220 15 = 8 ∧ acceleratedOrbit 15 5220 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5220) = 3 ^ 8 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5220.1, data_15_5220.2]

/-- Complete interval computation for depth 15, residue 5221. -/
theorem bounds_15_5221 : exactInterval 15 5221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5221 : oddCount 5221 15 = 8 ∧ acceleratedOrbit 15 5221 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5221) = 3 ^ 8 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5221.1, data_15_5221.2]

/-- Complete interval computation for depth 15, residue 5222. -/
theorem bounds_15_5222 : exactInterval 15 5222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5222 : oddCount 5222 15 = 8 ∧ acceleratedOrbit 15 5222 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5222) = 3 ^ 8 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5222.1, data_15_5222.2]

/-- Complete interval computation for depth 15, residue 5223. -/
theorem bounds_15_5223 : exactInterval 15 5223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5223 : oddCount 5223 15 = 11 ∧ acceleratedOrbit 15 5223 = 28244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5223) = 3 ^ 11 * m + 28244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5223.1, data_15_5223.2]

/-- Complete interval computation for depth 15, residue 5224. -/
theorem bounds_15_5224 : exactInterval 15 5224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5224 : oddCount 5224 15 = 5 ∧ acceleratedOrbit 15 5224 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5224) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5224.1, data_15_5224.2]

/-- Complete interval computation for depth 15, residue 5225. -/
theorem bounds_15_5225 : exactInterval 15 5225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5225 : oddCount 5225 15 = 10 ∧ acceleratedOrbit 15 5225 = 9422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5225) = 3 ^ 10 * m + 9422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5225.1, data_15_5225.2]

/-- Complete interval computation for depth 15, residue 5226. -/
theorem bounds_15_5226 : exactInterval 15 5226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5226 : oddCount 5226 15 = 5 ∧ acceleratedOrbit 15 5226 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5226) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5226.1, data_15_5226.2]

/-- Complete interval computation for depth 15, residue 5227. -/
theorem bounds_15_5227 : exactInterval 15 5227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5227 : oddCount 5227 15 = 7 ∧ acceleratedOrbit 15 5227 = 349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5227) = 3 ^ 7 * m + 349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5227.1, data_15_5227.2]

/-- Complete interval computation for depth 15, residue 5228. -/
theorem bounds_15_5228 : exactInterval 15 5228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5228 : oddCount 5228 15 = 11 ∧ acceleratedOrbit 15 5228 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5228) = 3 ^ 11 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5228.1, data_15_5228.2]

/-- Complete interval computation for depth 15, residue 5229. -/
theorem bounds_15_5229 : exactInterval 15 5229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5229 : oddCount 5229 15 = 11 ∧ acceleratedOrbit 15 5229 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5229) = 3 ^ 11 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5229.1, data_15_5229.2]

/-- Complete interval computation for depth 15, residue 5230. -/
theorem bounds_15_5230 : exactInterval 15 5230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5230 : oddCount 5230 15 = 11 ∧ acceleratedOrbit 15 5230 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5230) = 3 ^ 11 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5230.1, data_15_5230.2]

/-- Complete interval computation for depth 15, residue 5231. -/
theorem bounds_15_5231 : exactInterval 15 5231 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5231) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5231 : oddCount 5231 15 = 9 ∧ acceleratedOrbit 15 5231 = 3143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5231) = 3 ^ 9 * m + 3143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5231.1, data_15_5231.2]

/-- Complete interval computation for depth 15, residue 5232. -/
theorem bounds_15_5232 : exactInterval 15 5232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5232 : oddCount 5232 15 = 9 ∧ acceleratedOrbit 15 5232 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5232) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5232.1, data_15_5232.2]

/-- Complete interval computation for depth 15, residue 5233. -/
theorem bounds_15_5233 : exactInterval 15 5233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5233 : oddCount 5233 15 = 5 ∧ acceleratedOrbit 15 5233 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5233) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5233.1, data_15_5233.2]

/-- Complete interval computation for depth 15, residue 5234. -/
theorem bounds_15_5234 : exactInterval 15 5234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5234 : oddCount 5234 15 = 9 ∧ acceleratedOrbit 15 5234 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5234) = 3 ^ 9 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5234.1, data_15_5234.2]

/-- Complete interval computation for depth 15, residue 5235. -/
theorem bounds_15_5235 : exactInterval 15 5235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5235 : oddCount 5235 15 = 9 ∧ acceleratedOrbit 15 5235 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5235) = 3 ^ 9 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5235.1, data_15_5235.2]

/-- Complete interval computation for depth 15, residue 5236. -/
theorem bounds_15_5236 : exactInterval 15 5236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5236 : oddCount 5236 15 = 9 ∧ acceleratedOrbit 15 5236 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5236) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5236.1, data_15_5236.2]

/-- Complete interval computation for depth 15, residue 5237. -/
theorem bounds_15_5237 : exactInterval 15 5237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5237 : oddCount 5237 15 = 9 ∧ acceleratedOrbit 15 5237 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5237) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5237.1, data_15_5237.2]

/-- Complete interval computation for depth 15, residue 5238. -/
theorem bounds_15_5238 : exactInterval 15 5238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5238 : oddCount 5238 15 = 8 ∧ acceleratedOrbit 15 5238 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5238) = 3 ^ 8 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5238.1, data_15_5238.2]

/-- Complete interval computation for depth 15, residue 5239. -/
theorem bounds_15_5239 : exactInterval 15 5239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5239 : oddCount 5239 15 = 8 ∧ acceleratedOrbit 15 5239 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5239) = 3 ^ 8 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5239.1, data_15_5239.2]

/-- Complete interval computation for depth 15, residue 5240. -/
theorem bounds_15_5240 : exactInterval 15 5240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5240 : oddCount 5240 15 = 9 ∧ acceleratedOrbit 15 5240 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5240) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5240.1, data_15_5240.2]

/-- Complete interval computation for depth 15, residue 5241. -/
theorem bounds_15_5241 : exactInterval 15 5241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5241 : oddCount 5241 15 = 11 ∧ acceleratedOrbit 15 5241 = 28349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5241) = 3 ^ 11 * m + 28349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5241.1, data_15_5241.2]

end Collatz.Research.PassageAtlas.Batch0160
