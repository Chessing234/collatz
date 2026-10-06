import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0283

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9240. -/
theorem bounds_15_9240 : exactInterval 15 9240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9240 : oddCount 9240 15 = 4 ∧ acceleratedOrbit 15 9240 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9240) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9240.1, data_15_9240.2]

/-- Complete interval computation for depth 15, residue 9241. -/
theorem bounds_15_9241 : exactInterval 15 9241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9241 : oddCount 9241 15 = 7 ∧ acceleratedOrbit 15 9241 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9241) = 3 ^ 7 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9241.1, data_15_9241.2]

/-- Complete interval computation for depth 15, residue 9242. -/
theorem bounds_15_9242 : exactInterval 15 9242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9242 : oddCount 9242 15 = 4 ∧ acceleratedOrbit 15 9242 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9242) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9242.1, data_15_9242.2]

/-- Complete interval computation for depth 15, residue 9243. -/
theorem bounds_15_9243 : exactInterval 15 9243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9243 : oddCount 9243 15 = 13 ∧ acceleratedOrbit 15 9243 = 449792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9243) = 3 ^ 13 * m + 449792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9243.1, data_15_9243.2]

/-- Complete interval computation for depth 15, residue 9244. -/
theorem bounds_15_9244 : exactInterval 15 9244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9244 : oddCount 9244 15 = 8 ∧ acceleratedOrbit 15 9244 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9244) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9244.1, data_15_9244.2]

/-- Complete interval computation for depth 15, residue 9245. -/
theorem bounds_15_9245 : exactInterval 15 9245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9245 : oddCount 9245 15 = 8 ∧ acceleratedOrbit 15 9245 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9245) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9245.1, data_15_9245.2]

/-- Complete interval computation for depth 15, residue 9246. -/
theorem bounds_15_9246 : exactInterval 15 9246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9246 : oddCount 9246 15 = 8 ∧ acceleratedOrbit 15 9246 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9246) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9246.1, data_15_9246.2]

/-- Complete interval computation for depth 15, residue 9247. -/
theorem bounds_15_9247 : exactInterval 15 9247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9247 : oddCount 9247 15 = 11 ∧ acceleratedOrbit 15 9247 = 49997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9247) = 3 ^ 11 * m + 49997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9247.1, data_15_9247.2]

/-- Complete interval computation for depth 15, residue 9248. -/
theorem bounds_15_9248 : exactInterval 15 9248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9248 : oddCount 9248 15 = 4 ∧ acceleratedOrbit 15 9248 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9248) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9248.1, data_15_9248.2]

/-- Complete interval computation for depth 15, residue 9249. -/
theorem bounds_15_9249 : exactInterval 15 9249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9249 : oddCount 9249 15 = 10 ∧ acceleratedOrbit 15 9249 = 16676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9249) = 3 ^ 10 * m + 16676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9249.1, data_15_9249.2]

/-- Complete interval computation for depth 15, residue 9250. -/
theorem bounds_15_9250 : exactInterval 15 9250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9250 : oddCount 9250 15 = 4 ∧ acceleratedOrbit 15 9250 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9250) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9250.1, data_15_9250.2]

/-- Complete interval computation for depth 15, residue 9251. -/
theorem bounds_15_9251 : exactInterval 15 9251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9251 : oddCount 9251 15 = 4 ∧ acceleratedOrbit 15 9251 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9251) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9251.1, data_15_9251.2]

/-- Complete interval computation for depth 15, residue 9252. -/
theorem bounds_15_9252 : exactInterval 15 9252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9252 : oddCount 9252 15 = 6 ∧ acceleratedOrbit 15 9252 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9252) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9252.1, data_15_9252.2]

/-- Complete interval computation for depth 15, residue 9253. -/
theorem bounds_15_9253 : exactInterval 15 9253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9253 : oddCount 9253 15 = 6 ∧ acceleratedOrbit 15 9253 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9253) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9253.1, data_15_9253.2]

/-- Complete interval computation for depth 15, residue 9254. -/
theorem bounds_15_9254 : exactInterval 15 9254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9254 : oddCount 9254 15 = 6 ∧ acceleratedOrbit 15 9254 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9254) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9254.1, data_15_9254.2]

/-- Complete interval computation for depth 15, residue 9255. -/
theorem bounds_15_9255 : exactInterval 15 9255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9255 : oddCount 9255 15 = 10 ∧ acceleratedOrbit 15 9255 = 16685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9255) = 3 ^ 10 * m + 16685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9255.1, data_15_9255.2]

/-- Complete interval computation for depth 15, residue 9256. -/
theorem bounds_15_9256 : exactInterval 15 9256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9256 : oddCount 9256 15 = 4 ∧ acceleratedOrbit 15 9256 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9256) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9256.1, data_15_9256.2]

/-- Complete interval computation for depth 15, residue 9257. -/
theorem bounds_15_9257 : exactInterval 15 9257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9257 : oddCount 9257 15 = 11 ∧ acceleratedOrbit 15 9257 = 50057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9257) = 3 ^ 11 * m + 50057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9257.1, data_15_9257.2]

/-- Complete interval computation for depth 15, residue 9258. -/
theorem bounds_15_9258 : exactInterval 15 9258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9258 : oddCount 9258 15 = 4 ∧ acceleratedOrbit 15 9258 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9258) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9258.1, data_15_9258.2]

/-- Complete interval computation for depth 15, residue 9259. -/
theorem bounds_15_9259 : exactInterval 15 9259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9259 : oddCount 9259 15 = 8 ∧ acceleratedOrbit 15 9259 = 1856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9259) = 3 ^ 8 * m + 1856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9259.1, data_15_9259.2]

/-- Complete interval computation for depth 15, residue 9260. -/
theorem bounds_15_9260 : exactInterval 15 9260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9260 : oddCount 9260 15 = 7 ∧ acceleratedOrbit 15 9260 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9260) = 3 ^ 7 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9260.1, data_15_9260.2]

/-- Complete interval computation for depth 15, residue 9261. -/
theorem bounds_15_9261 : exactInterval 15 9261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9261 : oddCount 9261 15 = 7 ∧ acceleratedOrbit 15 9261 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9261) = 3 ^ 7 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9261.1, data_15_9261.2]

/-- Complete interval computation for depth 15, residue 9262. -/
theorem bounds_15_9262 : exactInterval 15 9262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9262 : oddCount 9262 15 = 7 ∧ acceleratedOrbit 15 9262 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9262) = 3 ^ 7 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9262.1, data_15_9262.2]

/-- Complete interval computation for depth 15, residue 9263. -/
theorem bounds_15_9263 : exactInterval 15 9263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9263 : oddCount 9263 15 = 8 ∧ acceleratedOrbit 15 9263 = 1855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9263) = 3 ^ 8 * m + 1855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9263.1, data_15_9263.2]

/-- Complete interval computation for depth 15, residue 9264. -/
theorem bounds_15_9264 : exactInterval 15 9264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9264 : oddCount 9264 15 = 4 ∧ acceleratedOrbit 15 9264 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9264) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9264.1, data_15_9264.2]

/-- Complete interval computation for depth 15, residue 9265. -/
theorem bounds_15_9265 : exactInterval 15 9265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9265 : oddCount 9265 15 = 7 ∧ acceleratedOrbit 15 9265 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9265) = 3 ^ 7 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9265.1, data_15_9265.2]

/-- Complete interval computation for depth 15, residue 9266. -/
theorem bounds_15_9266 : exactInterval 15 9266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9266 : oddCount 9266 15 = 7 ∧ acceleratedOrbit 15 9266 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9266) = 3 ^ 7 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9266.1, data_15_9266.2]

/-- Complete interval computation for depth 15, residue 9267. -/
theorem bounds_15_9267 : exactInterval 15 9267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9267 : oddCount 9267 15 = 7 ∧ acceleratedOrbit 15 9267 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9267) = 3 ^ 7 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9267.1, data_15_9267.2]

/-- Complete interval computation for depth 15, residue 9268. -/
theorem bounds_15_9268 : exactInterval 15 9268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9268 : oddCount 9268 15 = 4 ∧ acceleratedOrbit 15 9268 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9268) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9268.1, data_15_9268.2]

/-- Complete interval computation for depth 15, residue 9269. -/
theorem bounds_15_9269 : exactInterval 15 9269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9269 : oddCount 9269 15 = 4 ∧ acceleratedOrbit 15 9269 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9269) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9269.1, data_15_9269.2]

/-- Complete interval computation for depth 15, residue 9270. -/
theorem bounds_15_9270 : exactInterval 15 9270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9270 : oddCount 9270 15 = 10 ∧ acceleratedOrbit 15 9270 = 16712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9270) = 3 ^ 10 * m + 16712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9270.1, data_15_9270.2]

/-- Complete interval computation for depth 15, residue 9271. -/
theorem bounds_15_9271 : exactInterval 15 9271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9271 : oddCount 9271 15 = 10 ∧ acceleratedOrbit 15 9271 = 16712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9271) = 3 ^ 10 * m + 16712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9271.1, data_15_9271.2]

/-- Complete interval computation for depth 15, residue 9272. -/
theorem bounds_15_9272 : exactInterval 15 9272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9272 : oddCount 9272 15 = 8 ∧ acceleratedOrbit 15 9272 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9272) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9272.1, data_15_9272.2]

end Collatz.Research.PassageAtlas.Batch0283
