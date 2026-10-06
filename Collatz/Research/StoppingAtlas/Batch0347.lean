import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0347

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2242. -/
theorem bounds_12_2242 : exactInterval 12 2242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2242 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2242) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2242 : oddCount 2242 12 = 6 ∧ acceleratedOrbit 12 2242 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2242 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2242) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2242.1, data_12_2242.2]

/-- Complete interval computation for depth 12, residue 2243. -/
theorem bounds_12_2243 : exactInterval 12 2243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2243 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2243) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2243 : oddCount 2243 12 = 6 ∧ acceleratedOrbit 12 2243 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2243 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2243) = 3 ^ 6 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2243.1, data_12_2243.2]

/-- Complete interval computation for depth 12, residue 2244. -/
theorem bounds_12_2244 : exactInterval 12 2244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2244 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2244) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2244 : oddCount 2244 12 = 6 ∧ acceleratedOrbit 12 2244 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2244 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2244) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2244.1, data_12_2244.2]

/-- Complete interval computation for depth 12, residue 2245. -/
theorem bounds_12_2245 : exactInterval 12 2245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2245 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2245) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2245 : oddCount 2245 12 = 6 ∧ acceleratedOrbit 12 2245 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2245 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2245) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2245.1, data_12_2245.2]

/-- Complete interval computation for depth 12, residue 2246. -/
theorem bounds_12_2246 : exactInterval 12 2246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2246 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2246) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2246 : oddCount 2246 12 = 6 ∧ acceleratedOrbit 12 2246 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2246 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2246) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2246.1, data_12_2246.2]

/-- Complete interval computation for depth 12, residue 2247. -/
theorem bounds_12_2247 : exactInterval 12 2247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2247 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2247) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2247 : oddCount 2247 12 = 7 ∧ acceleratedOrbit 12 2247 = 1201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2247 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2247) = 3 ^ 7 * m + 1201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2247.1, data_12_2247.2]

/-- Complete interval computation for depth 12, residue 2248. -/
theorem bounds_12_2248 : exactInterval 12 2248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2248 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2248) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2248 : oddCount 2248 12 = 6 ∧ acceleratedOrbit 12 2248 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2248 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2248) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2248.1, data_12_2248.2]

/-- Complete interval computation for depth 12, residue 2249. -/
theorem bounds_12_2249 : exactInterval 12 2249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2249 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2249) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2249 : oddCount 2249 12 = 5 ∧ acceleratedOrbit 12 2249 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2249 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2249) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2249.1, data_12_2249.2]

/-- Complete interval computation for depth 12, residue 2250. -/
theorem bounds_12_2250 : exactInterval 12 2250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2250 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2250) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2250 : oddCount 2250 12 = 6 ∧ acceleratedOrbit 12 2250 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2250 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2250) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2250.1, data_12_2250.2]

/-- Complete interval computation for depth 12, residue 2251. -/
theorem bounds_12_2251 : exactInterval 12 2251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2251 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2251) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2251 : oddCount 2251 12 = 7 ∧ acceleratedOrbit 12 2251 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2251 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2251) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2251.1, data_12_2251.2]

/-- Complete interval computation for depth 12, residue 2252. -/
theorem bounds_12_2252 : exactInterval 12 2252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2252 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2252) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2252 : oddCount 2252 12 = 6 ∧ acceleratedOrbit 12 2252 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2252 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2252) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2252.1, data_12_2252.2]

/-- Complete interval computation for depth 12, residue 2253. -/
theorem bounds_12_2253 : exactInterval 12 2253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2253 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2253) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2253 : oddCount 2253 12 = 6 ∧ acceleratedOrbit 12 2253 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2253 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2253) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2253.1, data_12_2253.2]

/-- Complete interval computation for depth 12, residue 2254. -/
theorem bounds_12_2254 : exactInterval 12 2254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2254 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2254) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2254 : oddCount 2254 12 = 9 ∧ acceleratedOrbit 12 2254 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2254 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2254) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2254.1, data_12_2254.2]

/-- Complete interval computation for depth 12, residue 2255. -/
theorem bounds_12_2255 : exactInterval 12 2255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2255 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2255) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2255 : oddCount 2255 12 = 9 ∧ acceleratedOrbit 12 2255 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2255 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2255) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2255.1, data_12_2255.2]

/-- Complete interval computation for depth 12, residue 2256. -/
theorem bounds_12_2256 : exactInterval 12 2256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2256 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2256) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2256 : oddCount 2256 12 = 2 ∧ acceleratedOrbit 12 2256 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2256 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2256) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2256.1, data_12_2256.2]

end Collatz.Research.StoppingAtlas.Batch0347
