import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0613

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2232. -/
theorem bounds_13_2232 : exactInterval 13 2232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2232 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2232) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2232 : oddCount 2232 13 = 5 ∧ acceleratedOrbit 13 2232 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2232 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2232) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2232.1, data_13_2232.2]

/-- Complete interval computation for depth 13, residue 2233. -/
theorem bounds_13_2233 : exactInterval 13 2233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2233 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2233) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2233 : oddCount 2233 13 = 6 ∧ acceleratedOrbit 13 2233 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2233 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2233) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2233.1, data_13_2233.2]

/-- Complete interval computation for depth 13, residue 2234. -/
theorem bounds_13_2234 : exactInterval 13 2234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2234 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2234) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2234 : oddCount 2234 13 = 5 ∧ acceleratedOrbit 13 2234 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2234 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2234) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2234.1, data_13_2234.2]

/-- Complete interval computation for depth 13, residue 2235. -/
theorem bounds_13_2235 : exactInterval 13 2235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2235 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2235) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2235 : oddCount 2235 13 = 8 ∧ acceleratedOrbit 13 2235 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2235 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2235) = 3 ^ 8 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2235.1, data_13_2235.2]

/-- Complete interval computation for depth 13, residue 2236. -/
theorem bounds_13_2236 : exactInterval 13 2236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2236 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2236) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2236 : oddCount 2236 13 = 8 ∧ acceleratedOrbit 13 2236 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2236 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2236) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2236.1, data_13_2236.2]

/-- Complete interval computation for depth 13, residue 2237. -/
theorem bounds_13_2237 : exactInterval 13 2237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2237 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2237) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2237 : oddCount 2237 13 = 8 ∧ acceleratedOrbit 13 2237 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2237 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2237) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2237.1, data_13_2237.2]

/-- Complete interval computation for depth 13, residue 2238. -/
theorem bounds_13_2238 : exactInterval 13 2238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2238 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2238) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2238 : oddCount 2238 13 = 8 ∧ acceleratedOrbit 13 2238 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2238 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2238) = 3 ^ 8 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2238.1, data_13_2238.2]

/-- Complete interval computation for depth 13, residue 2239. -/
theorem bounds_13_2239 : exactInterval 13 2239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2239 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2239) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2239 : oddCount 2239 13 = 7 ∧ acceleratedOrbit 13 2239 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2239 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2239) = 3 ^ 7 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2239.1, data_13_2239.2]

/-- Complete interval computation for depth 13, residue 2240. -/
theorem bounds_13_2240 : exactInterval 13 2240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2240 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2240) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2240 : oddCount 2240 13 = 3 ∧ acceleratedOrbit 13 2240 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2240 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2240) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2240.1, data_13_2240.2]

/-- Complete interval computation for depth 13, residue 2241. -/
theorem bounds_13_2241 : exactInterval 13 2241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2241 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2241) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2241 : oddCount 2241 13 = 6 ∧ acceleratedOrbit 13 2241 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2241 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2241) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2241.1, data_13_2241.2]

/-- Complete interval computation for depth 13, residue 2242. -/
theorem bounds_13_2242 : exactInterval 13 2242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2242 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2242) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2242 : oddCount 2242 13 = 6 ∧ acceleratedOrbit 13 2242 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2242 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2242) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2242.1, data_13_2242.2]

/-- Complete interval computation for depth 13, residue 2243. -/
theorem bounds_13_2243 : exactInterval 13 2243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2243 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2243) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2243 : oddCount 2243 13 = 6 ∧ acceleratedOrbit 13 2243 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2243 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2243) = 3 ^ 6 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2243.1, data_13_2243.2]

/-- Complete interval computation for depth 13, residue 2244. -/
theorem bounds_13_2244 : exactInterval 13 2244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2244 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2244) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2244 : oddCount 2244 13 = 6 ∧ acceleratedOrbit 13 2244 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2244 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2244) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2244.1, data_13_2244.2]

/-- Complete interval computation for depth 13, residue 2245. -/
theorem bounds_13_2245 : exactInterval 13 2245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2245 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2245) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2245 : oddCount 2245 13 = 6 ∧ acceleratedOrbit 13 2245 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2245 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2245) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2245.1, data_13_2245.2]

/-- Complete interval computation for depth 13, residue 2246. -/
theorem bounds_13_2246 : exactInterval 13 2246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2246 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2246) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2246 : oddCount 2246 13 = 6 ∧ acceleratedOrbit 13 2246 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2246 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2246) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2246.1, data_13_2246.2]

end Collatz.Research.StoppingAtlas.Batch0613
