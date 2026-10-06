import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0069

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2228. -/
theorem bounds_15_2228 : exactInterval 15 2228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2228 : oddCount 2228 15 = 7 ∧ acceleratedOrbit 15 2228 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2228) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2228.1, data_15_2228.2]

/-- Complete interval computation for depth 15, residue 2229. -/
theorem bounds_15_2229 : exactInterval 15 2229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2229 : oddCount 2229 15 = 7 ∧ acceleratedOrbit 15 2229 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2229) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2229.1, data_15_2229.2]

/-- Complete interval computation for depth 15, residue 2230. -/
theorem bounds_15_2230 : exactInterval 15 2230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2230 : oddCount 2230 15 = 10 ∧ acceleratedOrbit 15 2230 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2230) = 3 ^ 10 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2230.1, data_15_2230.2]

/-- Complete interval computation for depth 15, residue 2231. -/
theorem bounds_15_2231 : exactInterval 15 2231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2231 : oddCount 2231 15 = 10 ∧ acceleratedOrbit 15 2231 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2231) = 3 ^ 10 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2231.1, data_15_2231.2]

/-- Complete interval computation for depth 15, residue 2232. -/
theorem bounds_15_2232 : exactInterval 15 2232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2232 : oddCount 2232 15 = 7 ∧ acceleratedOrbit 15 2232 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2232) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2232.1, data_15_2232.2]

/-- Complete interval computation for depth 15, residue 2233. -/
theorem bounds_15_2233 : exactInterval 15 2233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2233 : oddCount 2233 15 = 8 ∧ acceleratedOrbit 15 2233 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2233) = 3 ^ 8 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2233.1, data_15_2233.2]

/-- Complete interval computation for depth 15, residue 2234. -/
theorem bounds_15_2234 : exactInterval 15 2234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2234 : oddCount 2234 15 = 7 ∧ acceleratedOrbit 15 2234 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2234) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2234.1, data_15_2234.2]

/-- Complete interval computation for depth 15, residue 2235. -/
theorem bounds_15_2235 : exactInterval 15 2235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2235 : oddCount 2235 15 = 8 ∧ acceleratedOrbit 15 2235 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2235) = 3 ^ 8 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2235.1, data_15_2235.2]

/-- Complete interval computation for depth 15, residue 2236. -/
theorem bounds_15_2236 : exactInterval 15 2236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2236 : oddCount 2236 15 = 10 ∧ acceleratedOrbit 15 2236 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2236) = 3 ^ 10 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2236.1, data_15_2236.2]

/-- Complete interval computation for depth 15, residue 2237. -/
theorem bounds_15_2237 : exactInterval 15 2237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2237 : oddCount 2237 15 = 10 ∧ acceleratedOrbit 15 2237 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2237) = 3 ^ 10 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2237.1, data_15_2237.2]

/-- Complete interval computation for depth 15, residue 2238. -/
theorem bounds_15_2238 : exactInterval 15 2238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2238 : oddCount 2238 15 = 10 ∧ acceleratedOrbit 15 2238 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2238) = 3 ^ 10 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2238.1, data_15_2238.2]

/-- Complete interval computation for depth 15, residue 2239. -/
theorem bounds_15_2239 : exactInterval 15 2239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2239 : oddCount 2239 15 = 8 ∧ acceleratedOrbit 15 2239 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2239) = 3 ^ 8 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2239.1, data_15_2239.2]

/-- Complete interval computation for depth 15, residue 2240. -/
theorem bounds_15_2240 : exactInterval 15 2240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2240 : oddCount 2240 15 = 3 ∧ acceleratedOrbit 15 2240 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2240) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2240.1, data_15_2240.2]

/-- Complete interval computation for depth 15, residue 2241. -/
theorem bounds_15_2241 : exactInterval 15 2241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2241 : oddCount 2241 15 = 6 ∧ acceleratedOrbit 15 2241 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2241) = 3 ^ 6 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2241.1, data_15_2241.2]

/-- Complete interval computation for depth 15, residue 2242. -/
theorem bounds_15_2242 : exactInterval 15 2242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2242 : oddCount 2242 15 = 6 ∧ acceleratedOrbit 15 2242 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2242) = 3 ^ 6 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2242.1, data_15_2242.2]

/-- Complete interval computation for depth 15, residue 2243. -/
theorem bounds_15_2243 : exactInterval 15 2243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2243 : oddCount 2243 15 = 6 ∧ acceleratedOrbit 15 2243 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2243) = 3 ^ 6 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2243.1, data_15_2243.2]

/-- Complete interval computation for depth 15, residue 2244. -/
theorem bounds_15_2244 : exactInterval 15 2244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2244 : oddCount 2244 15 = 7 ∧ acceleratedOrbit 15 2244 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2244) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2244.1, data_15_2244.2]

/-- Complete interval computation for depth 15, residue 2245. -/
theorem bounds_15_2245 : exactInterval 15 2245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2245 : oddCount 2245 15 = 7 ∧ acceleratedOrbit 15 2245 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2245) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2245.1, data_15_2245.2]

/-- Complete interval computation for depth 15, residue 2246. -/
theorem bounds_15_2246 : exactInterval 15 2246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2246 : oddCount 2246 15 = 7 ∧ acceleratedOrbit 15 2246 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2246) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2246.1, data_15_2246.2]

/-- Complete interval computation for depth 15, residue 2247. -/
theorem bounds_15_2247 : exactInterval 15 2247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2247 : oddCount 2247 15 = 9 ∧ acceleratedOrbit 15 2247 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2247) = 3 ^ 9 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2247.1, data_15_2247.2]

/-- Complete interval computation for depth 15, residue 2248. -/
theorem bounds_15_2248 : exactInterval 15 2248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2248 : oddCount 2248 15 = 7 ∧ acceleratedOrbit 15 2248 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2248) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2248.1, data_15_2248.2]

/-- Complete interval computation for depth 15, residue 2249. -/
theorem bounds_15_2249 : exactInterval 15 2249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2249 : oddCount 2249 15 = 7 ∧ acceleratedOrbit 15 2249 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2249) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2249.1, data_15_2249.2]

/-- Complete interval computation for depth 15, residue 2250. -/
theorem bounds_15_2250 : exactInterval 15 2250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2250 : oddCount 2250 15 = 7 ∧ acceleratedOrbit 15 2250 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2250) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2250.1, data_15_2250.2]

/-- Complete interval computation for depth 15, residue 2251. -/
theorem bounds_15_2251 : exactInterval 15 2251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2251 : oddCount 2251 15 = 8 ∧ acceleratedOrbit 15 2251 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2251) = 3 ^ 8 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2251.1, data_15_2251.2]

/-- Complete interval computation for depth 15, residue 2252. -/
theorem bounds_15_2252 : exactInterval 15 2252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2252 : oddCount 2252 15 = 7 ∧ acceleratedOrbit 15 2252 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2252) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2252.1, data_15_2252.2]

/-- Complete interval computation for depth 15, residue 2253. -/
theorem bounds_15_2253 : exactInterval 15 2253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2253 : oddCount 2253 15 = 7 ∧ acceleratedOrbit 15 2253 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2253) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2253.1, data_15_2253.2]

/-- Complete interval computation for depth 15, residue 2254. -/
theorem bounds_15_2254 : exactInterval 15 2254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2254 : oddCount 2254 15 = 10 ∧ acceleratedOrbit 15 2254 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2254) = 3 ^ 10 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2254.1, data_15_2254.2]

/-- Complete interval computation for depth 15, residue 2255. -/
theorem bounds_15_2255 : exactInterval 15 2255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2255 : oddCount 2255 15 = 10 ∧ acceleratedOrbit 15 2255 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2255) = 3 ^ 10 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2255.1, data_15_2255.2]

/-- Complete interval computation for depth 15, residue 2256. -/
theorem bounds_15_2256 : exactInterval 15 2256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2256 : oddCount 2256 15 = 3 ∧ acceleratedOrbit 15 2256 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2256) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2256.1, data_15_2256.2]

/-- Complete interval computation for depth 15, residue 2257. -/
theorem bounds_15_2257 : exactInterval 15 2257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2257 : oddCount 2257 15 = 7 ∧ acceleratedOrbit 15 2257 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2257) = 3 ^ 7 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2257.1, data_15_2257.2]

/-- Complete interval computation for depth 15, residue 2258. -/
theorem bounds_15_2258 : exactInterval 15 2258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2258 : oddCount 2258 15 = 7 ∧ acceleratedOrbit 15 2258 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2258) = 3 ^ 7 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2258.1, data_15_2258.2]

/-- Complete interval computation for depth 15, residue 2259. -/
theorem bounds_15_2259 : exactInterval 15 2259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2259 : oddCount 2259 15 = 7 ∧ acceleratedOrbit 15 2259 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2259) = 3 ^ 7 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2259.1, data_15_2259.2]

end Collatz.Research.PassageAtlas.Batch0069
