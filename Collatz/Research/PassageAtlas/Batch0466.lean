import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0466

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15237. -/
theorem bounds_15_15237 : exactInterval 15 15237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15237 : oddCount 15237 15 = 8 ∧ acceleratedOrbit 15 15237 = 3053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15237) = 3 ^ 8 * m + 3053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15237.1, data_15_15237.2]

/-- Complete interval computation for depth 15, residue 15238. -/
theorem bounds_15_15238 : exactInterval 15 15238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15238 : oddCount 15238 15 = 8 ∧ acceleratedOrbit 15 15238 = 3053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15238) = 3 ^ 8 * m + 3053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15238.1, data_15_15238.2]

/-- Complete interval computation for depth 15, residue 15239. -/
theorem bounds_15_15239 : exactInterval 15 15239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15239 : oddCount 15239 15 = 8 ∧ acceleratedOrbit 15 15239 = 3053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15239) = 3 ^ 8 * m + 3053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15239.1, data_15_15239.2]

/-- Complete interval computation for depth 15, residue 15240. -/
theorem bounds_15_15240 : exactInterval 15 15240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15240 : oddCount 15240 15 = 4 ∧ acceleratedOrbit 15 15240 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15240) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15240.1, data_15_15240.2]

/-- Complete interval computation for depth 15, residue 15241. -/
theorem bounds_15_15241 : exactInterval 15 15241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15241 : oddCount 15241 15 = 10 ∧ acceleratedOrbit 15 15241 = 27469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15241) = 3 ^ 10 * m + 27469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15241.1, data_15_15241.2]

/-- Complete interval computation for depth 15, residue 15242. -/
theorem bounds_15_15242 : exactInterval 15 15242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15242 : oddCount 15242 15 = 4 ∧ acceleratedOrbit 15 15242 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15242) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15242.1, data_15_15242.2]

/-- Complete interval computation for depth 15, residue 15243. -/
theorem bounds_15_15243 : exactInterval 15 15243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15243 : oddCount 15243 15 = 9 ∧ acceleratedOrbit 15 15243 = 9158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15243) = 3 ^ 9 * m + 9158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15243.1, data_15_15243.2]

/-- Complete interval computation for depth 15, residue 15244. -/
theorem bounds_15_15244 : exactInterval 15 15244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15244 : oddCount 15244 15 = 4 ∧ acceleratedOrbit 15 15244 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15244) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15244.1, data_15_15244.2]

/-- Complete interval computation for depth 15, residue 15245. -/
theorem bounds_15_15245 : exactInterval 15 15245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15245 : oddCount 15245 15 = 4 ∧ acceleratedOrbit 15 15245 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15245) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15245.1, data_15_15245.2]

/-- Complete interval computation for depth 15, residue 15246. -/
theorem bounds_15_15246 : exactInterval 15 15246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15246 : oddCount 15246 15 = 7 ∧ acceleratedOrbit 15 15246 = 1018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15246) = 3 ^ 7 * m + 1018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15246.1, data_15_15246.2]

/-- Complete interval computation for depth 15, residue 15247. -/
theorem bounds_15_15247 : exactInterval 15 15247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15247 : oddCount 15247 15 = 7 ∧ acceleratedOrbit 15 15247 = 1018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15247) = 3 ^ 7 * m + 1018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15247.1, data_15_15247.2]

/-- Complete interval computation for depth 15, residue 15248. -/
theorem bounds_15_15248 : exactInterval 15 15248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15248 : oddCount 15248 15 = 6 ∧ acceleratedOrbit 15 15248 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15248) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15248.1, data_15_15248.2]

/-- Complete interval computation for depth 15, residue 15249. -/
theorem bounds_15_15249 : exactInterval 15 15249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15249 : oddCount 15249 15 = 7 ∧ acceleratedOrbit 15 15249 = 1019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15249) = 3 ^ 7 * m + 1019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15249.1, data_15_15249.2]

/-- Complete interval computation for depth 15, residue 15250. -/
theorem bounds_15_15250 : exactInterval 15 15250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15250 : oddCount 15250 15 = 7 ∧ acceleratedOrbit 15 15250 = 1019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15250) = 3 ^ 7 * m + 1019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15250.1, data_15_15250.2]

/-- Complete interval computation for depth 15, residue 15251. -/
theorem bounds_15_15251 : exactInterval 15 15251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15251 : oddCount 15251 15 = 7 ∧ acceleratedOrbit 15 15251 = 1019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15251) = 3 ^ 7 * m + 1019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15251.1, data_15_15251.2]

/-- Complete interval computation for depth 15, residue 15252. -/
theorem bounds_15_15252 : exactInterval 15 15252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15252 : oddCount 15252 15 = 6 ∧ acceleratedOrbit 15 15252 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15252) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15252.1, data_15_15252.2]

/-- Complete interval computation for depth 15, residue 15253. -/
theorem bounds_15_15253 : exactInterval 15 15253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15253 : oddCount 15253 15 = 6 ∧ acceleratedOrbit 15 15253 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15253) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15253.1, data_15_15253.2]

/-- Complete interval computation for depth 15, residue 15254. -/
theorem bounds_15_15254 : exactInterval 15 15254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15254 : oddCount 15254 15 = 7 ∧ acceleratedOrbit 15 15254 = 1019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15254) = 3 ^ 7 * m + 1019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15254.1, data_15_15254.2]

/-- Complete interval computation for depth 15, residue 15255. -/
theorem bounds_15_15255 : exactInterval 15 15255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15255 : oddCount 15255 15 = 7 ∧ acceleratedOrbit 15 15255 = 1019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15255) = 3 ^ 7 * m + 1019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15255.1, data_15_15255.2]

/-- Complete interval computation for depth 15, residue 15256. -/
theorem bounds_15_15256 : exactInterval 15 15256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15256 : oddCount 15256 15 = 6 ∧ acceleratedOrbit 15 15256 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15256) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15256.1, data_15_15256.2]

/-- Complete interval computation for depth 15, residue 15257. -/
theorem bounds_15_15257 : exactInterval 15 15257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15257 : oddCount 15257 15 = 7 ∧ acceleratedOrbit 15 15257 = 1019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15257) = 3 ^ 7 * m + 1019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15257.1, data_15_15257.2]

/-- Complete interval computation for depth 15, residue 15258. -/
theorem bounds_15_15258 : exactInterval 15 15258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15258 : oddCount 15258 15 = 6 ∧ acceleratedOrbit 15 15258 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15258) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15258.1, data_15_15258.2]

/-- Complete interval computation for depth 15, residue 15259. -/
theorem bounds_15_15259 : exactInterval 15 15259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15259 : oddCount 15259 15 = 7 ∧ acceleratedOrbit 15 15259 = 1019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15259) = 3 ^ 7 * m + 1019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15259.1, data_15_15259.2]

/-- Complete interval computation for depth 15, residue 15260. -/
theorem bounds_15_15260 : exactInterval 15 15260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15260 : oddCount 15260 15 = 9 ∧ acceleratedOrbit 15 15260 = 9170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15260) = 3 ^ 9 * m + 9170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15260.1, data_15_15260.2]

/-- Complete interval computation for depth 15, residue 15261. -/
theorem bounds_15_15261 : exactInterval 15 15261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15261 : oddCount 15261 15 = 9 ∧ acceleratedOrbit 15 15261 = 9170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15261) = 3 ^ 9 * m + 9170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15261.1, data_15_15261.2]

/-- Complete interval computation for depth 15, residue 15262. -/
theorem bounds_15_15262 : exactInterval 15 15262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15262 : oddCount 15262 15 = 9 ∧ acceleratedOrbit 15 15262 = 9170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15262) = 3 ^ 9 * m + 9170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15262.1, data_15_15262.2]

/-- Complete interval computation for depth 15, residue 15263. -/
theorem bounds_15_15263 : exactInterval 15 15263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15263 : oddCount 15263 15 = 9 ∧ acceleratedOrbit 15 15263 = 9170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15263) = 3 ^ 9 * m + 9170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15263.1, data_15_15263.2]

/-- Complete interval computation for depth 15, residue 15264. -/
theorem bounds_15_15264 : exactInterval 15 15264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15264 : oddCount 15264 15 = 4 ∧ acceleratedOrbit 15 15264 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15264) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15264.1, data_15_15264.2]

/-- Complete interval computation for depth 15, residue 15265. -/
theorem bounds_15_15265 : exactInterval 15 15265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15265 : oddCount 15265 15 = 9 ∧ acceleratedOrbit 15 15265 = 9173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15265) = 3 ^ 9 * m + 9173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15265.1, data_15_15265.2]

/-- Complete interval computation for depth 15, residue 15266. -/
theorem bounds_15_15266 : exactInterval 15 15266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15266 : oddCount 15266 15 = 6 ∧ acceleratedOrbit 15 15266 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15266) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15266.1, data_15_15266.2]

/-- Complete interval computation for depth 15, residue 15267. -/
theorem bounds_15_15267 : exactInterval 15 15267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15267 : oddCount 15267 15 = 6 ∧ acceleratedOrbit 15 15267 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15267) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15267.1, data_15_15267.2]

/-- Complete interval computation for depth 15, residue 15268. -/
theorem bounds_15_15268 : exactInterval 15 15268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15268 : oddCount 15268 15 = 8 ∧ acceleratedOrbit 15 15268 = 3059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15268) = 3 ^ 8 * m + 3059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15268.1, data_15_15268.2]

end Collatz.Research.PassageAtlas.Batch0466
