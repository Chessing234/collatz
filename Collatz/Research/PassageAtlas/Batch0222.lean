import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0222

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7241. -/
theorem bounds_15_7241 : exactInterval 15 7241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7241 : oddCount 7241 15 = 10 ∧ acceleratedOrbit 15 7241 = 13054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7241) = 3 ^ 10 * m + 13054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7241.1, data_15_7241.2]

/-- Complete interval computation for depth 15, residue 7242. -/
theorem bounds_15_7242 : exactInterval 15 7242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7242 : oddCount 7242 15 = 8 ∧ acceleratedOrbit 15 7242 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7242) = 3 ^ 8 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7242.1, data_15_7242.2]

/-- Complete interval computation for depth 15, residue 7243. -/
theorem bounds_15_7243 : exactInterval 15 7243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7243 : oddCount 7243 15 = 8 ∧ acceleratedOrbit 15 7243 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7243) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7243.1, data_15_7243.2]

/-- Complete interval computation for depth 15, residue 7244. -/
theorem bounds_15_7244 : exactInterval 15 7244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7244 : oddCount 7244 15 = 8 ∧ acceleratedOrbit 15 7244 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7244) = 3 ^ 8 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7244.1, data_15_7244.2]

/-- Complete interval computation for depth 15, residue 7245. -/
theorem bounds_15_7245 : exactInterval 15 7245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7245 : oddCount 7245 15 = 8 ∧ acceleratedOrbit 15 7245 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7245) = 3 ^ 8 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7245.1, data_15_7245.2]

/-- Complete interval computation for depth 15, residue 7246. -/
theorem bounds_15_7246 : exactInterval 15 7246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7246 : oddCount 7246 15 = 7 ∧ acceleratedOrbit 15 7246 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7246) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7246.1, data_15_7246.2]

/-- Complete interval computation for depth 15, residue 7247. -/
theorem bounds_15_7247 : exactInterval 15 7247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7247 : oddCount 7247 15 = 7 ∧ acceleratedOrbit 15 7247 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7247) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7247.1, data_15_7247.2]

/-- Complete interval computation for depth 15, residue 7248. -/
theorem bounds_15_7248 : exactInterval 15 7248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7248 : oddCount 7248 15 = 2 ∧ acceleratedOrbit 15 7248 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7248) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7248.1, data_15_7248.2]

/-- Complete interval computation for depth 15, residue 7249. -/
theorem bounds_15_7249 : exactInterval 15 7249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7249 : oddCount 7249 15 = 8 ∧ acceleratedOrbit 15 7249 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7249) = 3 ^ 8 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7249.1, data_15_7249.2]

/-- Complete interval computation for depth 15, residue 7250. -/
theorem bounds_15_7250 : exactInterval 15 7250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7250 : oddCount 7250 15 = 9 ∧ acceleratedOrbit 15 7250 = 4357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7250) = 3 ^ 9 * m + 4357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7250.1, data_15_7250.2]

/-- Complete interval computation for depth 15, residue 7251. -/
theorem bounds_15_7251 : exactInterval 15 7251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7251 : oddCount 7251 15 = 9 ∧ acceleratedOrbit 15 7251 = 4357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7251) = 3 ^ 9 * m + 4357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7251.1, data_15_7251.2]

/-- Complete interval computation for depth 15, residue 7252. -/
theorem bounds_15_7252 : exactInterval 15 7252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7252 : oddCount 7252 15 = 2 ∧ acceleratedOrbit 15 7252 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7252) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7252.1, data_15_7252.2]

/-- Complete interval computation for depth 15, residue 7253. -/
theorem bounds_15_7253 : exactInterval 15 7253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7253 : oddCount 7253 15 = 2 ∧ acceleratedOrbit 15 7253 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7253) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7253.1, data_15_7253.2]

/-- Complete interval computation for depth 15, residue 7254. -/
theorem bounds_15_7254 : exactInterval 15 7254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7254 : oddCount 7254 15 = 8 ∧ acceleratedOrbit 15 7254 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7254) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7254.1, data_15_7254.2]

/-- Complete interval computation for depth 15, residue 7255. -/
theorem bounds_15_7255 : exactInterval 15 7255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7255 : oddCount 7255 15 = 8 ∧ acceleratedOrbit 15 7255 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7255) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7255.1, data_15_7255.2]

/-- Complete interval computation for depth 15, residue 7256. -/
theorem bounds_15_7256 : exactInterval 15 7256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7256 : oddCount 7256 15 = 9 ∧ acceleratedOrbit 15 7256 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7256) = 3 ^ 9 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7256.1, data_15_7256.2]

/-- Complete interval computation for depth 15, residue 7257. -/
theorem bounds_15_7257 : exactInterval 15 7257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7257 : oddCount 7257 15 = 9 ∧ acceleratedOrbit 15 7257 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7257) = 3 ^ 9 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7257.1, data_15_7257.2]

/-- Complete interval computation for depth 15, residue 7258. -/
theorem bounds_15_7258 : exactInterval 15 7258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7258 : oddCount 7258 15 = 9 ∧ acceleratedOrbit 15 7258 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7258) = 3 ^ 9 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7258.1, data_15_7258.2]

/-- Complete interval computation for depth 15, residue 7259. -/
theorem bounds_15_7259 : exactInterval 15 7259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7259 : oddCount 7259 15 = 10 ∧ acceleratedOrbit 15 7259 = 13085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7259) = 3 ^ 10 * m + 13085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7259.1, data_15_7259.2]

/-- Complete interval computation for depth 15, residue 7260. -/
theorem bounds_15_7260 : exactInterval 15 7260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7260 : oddCount 7260 15 = 9 ∧ acceleratedOrbit 15 7260 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7260) = 3 ^ 9 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7260.1, data_15_7260.2]

/-- Complete interval computation for depth 15, residue 7261. -/
theorem bounds_15_7261 : exactInterval 15 7261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7261 : oddCount 7261 15 = 9 ∧ acceleratedOrbit 15 7261 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7261) = 3 ^ 9 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7261.1, data_15_7261.2]

/-- Complete interval computation for depth 15, residue 7262. -/
theorem bounds_15_7262 : exactInterval 15 7262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7262 : oddCount 7262 15 = 11 ∧ acceleratedOrbit 15 7262 = 39275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7262) = 3 ^ 11 * m + 39275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7262.1, data_15_7262.2]

/-- Complete interval computation for depth 15, residue 7263. -/
theorem bounds_15_7263 : exactInterval 15 7263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7263 : oddCount 7263 15 = 11 ∧ acceleratedOrbit 15 7263 = 39275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7263) = 3 ^ 11 * m + 39275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7263.1, data_15_7263.2]

/-- Complete interval computation for depth 15, residue 7264. -/
theorem bounds_15_7264 : exactInterval 15 7264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7264 : oddCount 7264 15 = 2 ∧ acceleratedOrbit 15 7264 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7264) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7264.1, data_15_7264.2]

/-- Complete interval computation for depth 15, residue 7265. -/
theorem bounds_15_7265 : exactInterval 15 7265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7265 : oddCount 7265 15 = 9 ∧ acceleratedOrbit 15 7265 = 4367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7265) = 3 ^ 9 * m + 4367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7265.1, data_15_7265.2]

/-- Complete interval computation for depth 15, residue 7266. -/
theorem bounds_15_7266 : exactInterval 15 7266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7266 : oddCount 7266 15 = 10 ∧ acceleratedOrbit 15 7266 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7266) = 3 ^ 10 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7266.1, data_15_7266.2]

/-- Complete interval computation for depth 15, residue 7267. -/
theorem bounds_15_7267 : exactInterval 15 7267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7267 : oddCount 7267 15 = 10 ∧ acceleratedOrbit 15 7267 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7267) = 3 ^ 10 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7267.1, data_15_7267.2]

/-- Complete interval computation for depth 15, residue 7268. -/
theorem bounds_15_7268 : exactInterval 15 7268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7268 : oddCount 7268 15 = 10 ∧ acceleratedOrbit 15 7268 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7268) = 3 ^ 10 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7268.1, data_15_7268.2]

/-- Complete interval computation for depth 15, residue 7269. -/
theorem bounds_15_7269 : exactInterval 15 7269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7269 : oddCount 7269 15 = 10 ∧ acceleratedOrbit 15 7269 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7269) = 3 ^ 10 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7269.1, data_15_7269.2]

/-- Complete interval computation for depth 15, residue 7270. -/
theorem bounds_15_7270 : exactInterval 15 7270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7270 : oddCount 7270 15 = 10 ∧ acceleratedOrbit 15 7270 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7270) = 3 ^ 10 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7270.1, data_15_7270.2]

/-- Complete interval computation for depth 15, residue 7271. -/
theorem bounds_15_7271 : exactInterval 15 7271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7271 : oddCount 7271 15 = 10 ∧ acceleratedOrbit 15 7271 = 13105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7271) = 3 ^ 10 * m + 13105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7271.1, data_15_7271.2]

/-- Complete interval computation for depth 15, residue 7272. -/
theorem bounds_15_7272 : exactInterval 15 7272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7272 : oddCount 7272 15 = 2 ∧ acceleratedOrbit 15 7272 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7272) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7272.1, data_15_7272.2]

/-- Complete interval computation for depth 15, residue 7273. -/
theorem bounds_15_7273 : exactInterval 15 7273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7273 : oddCount 7273 15 = 10 ∧ acceleratedOrbit 15 7273 = 13112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7273) = 3 ^ 10 * m + 13112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7273.1, data_15_7273.2]

end Collatz.Research.PassageAtlas.Batch0222
