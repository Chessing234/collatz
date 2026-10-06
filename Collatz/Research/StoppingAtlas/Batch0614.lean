import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0614

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2247. -/
theorem bounds_13_2247 : exactInterval 13 2247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2247 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2247) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2247 : oddCount 2247 13 = 8 ∧ acceleratedOrbit 13 2247 = 1802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2247 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2247) = 3 ^ 8 * m + 1802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2247.1, data_13_2247.2]

/-- Complete interval computation for depth 13, residue 2248. -/
theorem bounds_13_2248 : exactInterval 13 2248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2248 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2248) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2248 : oddCount 2248 13 = 6 ∧ acceleratedOrbit 13 2248 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2248 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2248) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2248.1, data_13_2248.2]

/-- Complete interval computation for depth 13, residue 2249. -/
theorem bounds_13_2249 : exactInterval 13 2249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2249 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2249) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2249 : oddCount 2249 13 = 5 ∧ acceleratedOrbit 13 2249 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2249 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2249) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2249.1, data_13_2249.2]

/-- Complete interval computation for depth 13, residue 2250. -/
theorem bounds_13_2250 : exactInterval 13 2250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2250 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2250) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2250 : oddCount 2250 13 = 6 ∧ acceleratedOrbit 13 2250 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2250 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2250) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2250.1, data_13_2250.2]

/-- Complete interval computation for depth 13, residue 2251. -/
theorem bounds_13_2251 : exactInterval 13 2251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2251 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2251) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2251 : oddCount 2251 13 = 8 ∧ acceleratedOrbit 13 2251 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2251 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2251) = 3 ^ 8 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2251.1, data_13_2251.2]

/-- Complete interval computation for depth 13, residue 2252. -/
theorem bounds_13_2252 : exactInterval 13 2252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2252 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2252) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2252 : oddCount 2252 13 = 6 ∧ acceleratedOrbit 13 2252 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2252 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2252) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2252.1, data_13_2252.2]

/-- Complete interval computation for depth 13, residue 2253. -/
theorem bounds_13_2253 : exactInterval 13 2253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2253 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2253) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2253 : oddCount 2253 13 = 6 ∧ acceleratedOrbit 13 2253 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2253 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2253) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2253.1, data_13_2253.2]

/-- Complete interval computation for depth 13, residue 2254. -/
theorem bounds_13_2254 : exactInterval 13 2254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2254 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2254) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2254 : oddCount 2254 13 = 9 ∧ acceleratedOrbit 13 2254 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2254 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2254) = 3 ^ 9 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2254.1, data_13_2254.2]

/-- Complete interval computation for depth 13, residue 2255. -/
theorem bounds_13_2255 : exactInterval 13 2255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2255 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2255) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2255 : oddCount 2255 13 = 9 ∧ acceleratedOrbit 13 2255 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2255 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2255) = 3 ^ 9 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2255.1, data_13_2255.2]

/-- Complete interval computation for depth 13, residue 2256. -/
theorem bounds_13_2256 : exactInterval 13 2256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2256 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2256) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2256 : oddCount 2256 13 = 3 ∧ acceleratedOrbit 13 2256 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2256 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2256) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2256.1, data_13_2256.2]

/-- Complete interval computation for depth 13, residue 2257. -/
theorem bounds_13_2257 : exactInterval 13 2257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2257 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2257) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2257 : oddCount 2257 13 = 7 ∧ acceleratedOrbit 13 2257 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2257 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2257) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2257.1, data_13_2257.2]

/-- Complete interval computation for depth 13, residue 2258. -/
theorem bounds_13_2258 : exactInterval 13 2258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2258 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2258) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2258 : oddCount 2258 13 = 7 ∧ acceleratedOrbit 13 2258 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2258 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2258) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2258.1, data_13_2258.2]

/-- Complete interval computation for depth 13, residue 2259. -/
theorem bounds_13_2259 : exactInterval 13 2259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2259 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2259) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2259 : oddCount 2259 13 = 7 ∧ acceleratedOrbit 13 2259 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2259 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2259) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2259.1, data_13_2259.2]

/-- Complete interval computation for depth 13, residue 2260. -/
theorem bounds_13_2260 : exactInterval 13 2260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2260 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2260) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2260 : oddCount 2260 13 = 3 ∧ acceleratedOrbit 13 2260 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2260 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2260) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2260.1, data_13_2260.2]

/-- Complete interval computation for depth 13, residue 2261. -/
theorem bounds_13_2261 : exactInterval 13 2261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2261 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2261) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2261 : oddCount 2261 13 = 3 ∧ acceleratedOrbit 13 2261 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2261 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2261) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2261.1, data_13_2261.2]

/-- Complete interval computation for depth 13, residue 2262. -/
theorem bounds_13_2262 : exactInterval 13 2262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2262 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2262) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2262 : oddCount 2262 13 = 7 ∧ acceleratedOrbit 13 2262 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2262 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2262) = 3 ^ 7 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2262.1, data_13_2262.2]

end Collatz.Research.StoppingAtlas.Batch0614
