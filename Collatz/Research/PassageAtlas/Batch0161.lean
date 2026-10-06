import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0161

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5242. -/
theorem bounds_15_5242 : exactInterval 15 5242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5242 : oddCount 5242 15 = 9 ∧ acceleratedOrbit 15 5242 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5242) = 3 ^ 9 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5242.1, data_15_5242.2]

/-- Complete interval computation for depth 15, residue 5243. -/
theorem bounds_15_5243 : exactInterval 15 5243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5243 : oddCount 5243 15 = 9 ∧ acceleratedOrbit 15 5243 = 3152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5243) = 3 ^ 9 * m + 3152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5243.1, data_15_5243.2]

/-- Complete interval computation for depth 15, residue 5244. -/
theorem bounds_15_5244 : exactInterval 15 5244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5244 : oddCount 5244 15 = 8 ∧ acceleratedOrbit 15 5244 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5244) = 3 ^ 8 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5244.1, data_15_5244.2]

/-- Complete interval computation for depth 15, residue 5245. -/
theorem bounds_15_5245 : exactInterval 15 5245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5245 : oddCount 5245 15 = 8 ∧ acceleratedOrbit 15 5245 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5245) = 3 ^ 8 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5245.1, data_15_5245.2]

/-- Complete interval computation for depth 15, residue 5246. -/
theorem bounds_15_5246 : exactInterval 15 5246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5246 : oddCount 5246 15 = 8 ∧ acceleratedOrbit 15 5246 = 1052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5246) = 3 ^ 8 * m + 1052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5246.1, data_15_5246.2]

/-- Complete interval computation for depth 15, residue 5247. -/
theorem bounds_15_5247 : exactInterval 15 5247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5247 : oddCount 5247 15 = 11 ∧ acceleratedOrbit 15 5247 = 28372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5247) = 3 ^ 11 * m + 28372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5247.1, data_15_5247.2]

/-- Complete interval computation for depth 15, residue 5248. -/
theorem bounds_15_5248 : exactInterval 15 5248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5248 : oddCount 5248 15 = 6 ∧ acceleratedOrbit 15 5248 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5248) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5248.1, data_15_5248.2]

/-- Complete interval computation for depth 15, residue 5249. -/
theorem bounds_15_5249 : exactInterval 15 5249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5249 : oddCount 5249 15 = 10 ∧ acceleratedOrbit 15 5249 = 9467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5249) = 3 ^ 10 * m + 9467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5249.1, data_15_5249.2]

/-- Complete interval computation for depth 15, residue 5250. -/
theorem bounds_15_5250 : exactInterval 15 5250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5250 : oddCount 5250 15 = 4 ∧ acceleratedOrbit 15 5250 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5250) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5250.1, data_15_5250.2]

/-- Complete interval computation for depth 15, residue 5251. -/
theorem bounds_15_5251 : exactInterval 15 5251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5251 : oddCount 5251 15 = 4 ∧ acceleratedOrbit 15 5251 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5251) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5251.1, data_15_5251.2]

/-- Complete interval computation for depth 15, residue 5252. -/
theorem bounds_15_5252 : exactInterval 15 5252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5252 : oddCount 5252 15 = 4 ∧ acceleratedOrbit 15 5252 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5252) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5252.1, data_15_5252.2]

/-- Complete interval computation for depth 15, residue 5253. -/
theorem bounds_15_5253 : exactInterval 15 5253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5253 : oddCount 5253 15 = 4 ∧ acceleratedOrbit 15 5253 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5253) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5253.1, data_15_5253.2]

/-- Complete interval computation for depth 15, residue 5254. -/
theorem bounds_15_5254 : exactInterval 15 5254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5254 : oddCount 5254 15 = 4 ∧ acceleratedOrbit 15 5254 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5254) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5254.1, data_15_5254.2]

/-- Complete interval computation for depth 15, residue 5255. -/
theorem bounds_15_5255 : exactInterval 15 5255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5255 : oddCount 5255 15 = 11 ∧ acceleratedOrbit 15 5255 = 28430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5255) = 3 ^ 11 * m + 28430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5255.1, data_15_5255.2]

/-- Complete interval computation for depth 15, residue 5256. -/
theorem bounds_15_5256 : exactInterval 15 5256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5256 : oddCount 5256 15 = 6 ∧ acceleratedOrbit 15 5256 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5256) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5256.1, data_15_5256.2]

/-- Complete interval computation for depth 15, residue 5257. -/
theorem bounds_15_5257 : exactInterval 15 5257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5257 : oddCount 5257 15 = 13 ∧ acceleratedOrbit 15 5257 = 255878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5257) = 3 ^ 13 * m + 255878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5257.1, data_15_5257.2]

/-- Complete interval computation for depth 15, residue 5258. -/
theorem bounds_15_5258 : exactInterval 15 5258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5258 : oddCount 5258 15 = 6 ∧ acceleratedOrbit 15 5258 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5258) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5258.1, data_15_5258.2]

/-- Complete interval computation for depth 15, residue 5259. -/
theorem bounds_15_5259 : exactInterval 15 5259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5259 : oddCount 5259 15 = 8 ∧ acceleratedOrbit 15 5259 = 1054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5259) = 3 ^ 8 * m + 1054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5259.1, data_15_5259.2]

/-- Complete interval computation for depth 15, residue 5260. -/
theorem bounds_15_5260 : exactInterval 15 5260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5260 : oddCount 5260 15 = 6 ∧ acceleratedOrbit 15 5260 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5260) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5260.1, data_15_5260.2]

/-- Complete interval computation for depth 15, residue 5261. -/
theorem bounds_15_5261 : exactInterval 15 5261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5261 : oddCount 5261 15 = 6 ∧ acceleratedOrbit 15 5261 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5261) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5261.1, data_15_5261.2]

/-- Complete interval computation for depth 15, residue 5262. -/
theorem bounds_15_5262 : exactInterval 15 5262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5262 : oddCount 5262 15 = 8 ∧ acceleratedOrbit 15 5262 = 1055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5262) = 3 ^ 8 * m + 1055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5262.1, data_15_5262.2]

/-- Complete interval computation for depth 15, residue 5263. -/
theorem bounds_15_5263 : exactInterval 15 5263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5263 : oddCount 5263 15 = 8 ∧ acceleratedOrbit 15 5263 = 1055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5263) = 3 ^ 8 * m + 1055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5263.1, data_15_5263.2]

/-- Complete interval computation for depth 15, residue 5264. -/
theorem bounds_15_5264 : exactInterval 15 5264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5264 : oddCount 5264 15 = 6 ∧ acceleratedOrbit 15 5264 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5264) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5264.1, data_15_5264.2]

/-- Complete interval computation for depth 15, residue 5265. -/
theorem bounds_15_5265 : exactInterval 15 5265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5265 : oddCount 5265 15 = 7 ∧ acceleratedOrbit 15 5265 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5265) = 3 ^ 7 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5265.1, data_15_5265.2]

/-- Complete interval computation for depth 15, residue 5266. -/
theorem bounds_15_5266 : exactInterval 15 5266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5266 : oddCount 5266 15 = 7 ∧ acceleratedOrbit 15 5266 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5266) = 3 ^ 7 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5266.1, data_15_5266.2]

/-- Complete interval computation for depth 15, residue 5267. -/
theorem bounds_15_5267 : exactInterval 15 5267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5267 : oddCount 5267 15 = 7 ∧ acceleratedOrbit 15 5267 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5267) = 3 ^ 7 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5267.1, data_15_5267.2]

/-- Complete interval computation for depth 15, residue 5268. -/
theorem bounds_15_5268 : exactInterval 15 5268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5268 : oddCount 5268 15 = 6 ∧ acceleratedOrbit 15 5268 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5268) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5268.1, data_15_5268.2]

/-- Complete interval computation for depth 15, residue 5269. -/
theorem bounds_15_5269 : exactInterval 15 5269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5269 : oddCount 5269 15 = 6 ∧ acceleratedOrbit 15 5269 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5269) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5269.1, data_15_5269.2]

/-- Complete interval computation for depth 15, residue 5270. -/
theorem bounds_15_5270 : exactInterval 15 5270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5270 : oddCount 5270 15 = 6 ∧ acceleratedOrbit 15 5270 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5270) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5270.1, data_15_5270.2]

/-- Complete interval computation for depth 15, residue 5271. -/
theorem bounds_15_5271 : exactInterval 15 5271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5271 : oddCount 5271 15 = 6 ∧ acceleratedOrbit 15 5271 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5271) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5271.1, data_15_5271.2]

/-- Complete interval computation for depth 15, residue 5272. -/
theorem bounds_15_5272 : exactInterval 15 5272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5272 : oddCount 5272 15 = 6 ∧ acceleratedOrbit 15 5272 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5272) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5272.1, data_15_5272.2]

/-- Complete interval computation for depth 15, residue 5273. -/
theorem bounds_15_5273 : exactInterval 15 5273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5273 : oddCount 5273 15 = 7 ∧ acceleratedOrbit 15 5273 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5273) = 3 ^ 7 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5273.1, data_15_5273.2]

/-- Complete interval computation for depth 15, residue 5274. -/
theorem bounds_15_5274 : exactInterval 15 5274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5274 : oddCount 5274 15 = 6 ∧ acceleratedOrbit 15 5274 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5274) = 3 ^ 6 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5274.1, data_15_5274.2]

end Collatz.Research.PassageAtlas.Batch0161
