import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0588

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19234. -/
theorem bounds_15_19234 : exactInterval 15 19234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19234 : oddCount 19234 15 = 7 ∧ acceleratedOrbit 15 19234 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19234) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19234.1, data_15_19234.2]

/-- Complete interval computation for depth 15, residue 19235. -/
theorem bounds_15_19235 : exactInterval 15 19235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19235 : oddCount 19235 15 = 7 ∧ acceleratedOrbit 15 19235 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19235) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19235.1, data_15_19235.2]

/-- Complete interval computation for depth 15, residue 19236. -/
theorem bounds_15_19236 : exactInterval 15 19236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19236 : oddCount 19236 15 = 7 ∧ acceleratedOrbit 15 19236 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19236) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19236.1, data_15_19236.2]

/-- Complete interval computation for depth 15, residue 19237. -/
theorem bounds_15_19237 : exactInterval 15 19237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19237 : oddCount 19237 15 = 7 ∧ acceleratedOrbit 15 19237 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19237) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19237.1, data_15_19237.2]

/-- Complete interval computation for depth 15, residue 19238. -/
theorem bounds_15_19238 : exactInterval 15 19238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19238 : oddCount 19238 15 = 7 ∧ acceleratedOrbit 15 19238 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19238) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19238.1, data_15_19238.2]

/-- Complete interval computation for depth 15, residue 19239. -/
theorem bounds_15_19239 : exactInterval 15 19239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19239 : oddCount 19239 15 = 9 ∧ acceleratedOrbit 15 19239 = 11558 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19239) = 3 ^ 9 * m + 11558 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19239.1, data_15_19239.2]

/-- Complete interval computation for depth 15, residue 19240. -/
theorem bounds_15_19240 : exactInterval 15 19240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19240 : oddCount 19240 15 = 6 ∧ acceleratedOrbit 15 19240 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19240) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19240.1, data_15_19240.2]

/-- Complete interval computation for depth 15, residue 19241. -/
theorem bounds_15_19241 : exactInterval 15 19241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19241 : oddCount 19241 15 = 8 ∧ acceleratedOrbit 15 19241 = 3853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19241) = 3 ^ 8 * m + 3853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19241.1, data_15_19241.2]

/-- Complete interval computation for depth 15, residue 19242. -/
theorem bounds_15_19242 : exactInterval 15 19242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19242 : oddCount 19242 15 = 6 ∧ acceleratedOrbit 15 19242 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19242) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19242.1, data_15_19242.2]

/-- Complete interval computation for depth 15, residue 19243. -/
theorem bounds_15_19243 : exactInterval 15 19243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19243 : oddCount 19243 15 = 8 ∧ acceleratedOrbit 15 19243 = 3854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19243) = 3 ^ 8 * m + 3854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19243.1, data_15_19243.2]

/-- Complete interval computation for depth 15, residue 19244. -/
theorem bounds_15_19244 : exactInterval 15 19244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19244 : oddCount 19244 15 = 7 ∧ acceleratedOrbit 15 19244 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19244) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19244.1, data_15_19244.2]

/-- Complete interval computation for depth 15, residue 19245. -/
theorem bounds_15_19245 : exactInterval 15 19245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19245 : oddCount 19245 15 = 7 ∧ acceleratedOrbit 15 19245 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19245) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19245.1, data_15_19245.2]

/-- Complete interval computation for depth 15, residue 19246. -/
theorem bounds_15_19246 : exactInterval 15 19246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19246 : oddCount 19246 15 = 7 ∧ acceleratedOrbit 15 19246 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19246) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19246.1, data_15_19246.2]

/-- Complete interval computation for depth 15, residue 19247. -/
theorem bounds_15_19247 : exactInterval 15 19247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19247 : oddCount 19247 15 = 10 ∧ acceleratedOrbit 15 19247 = 34688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19247) = 3 ^ 10 * m + 34688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19247.1, data_15_19247.2]

/-- Complete interval computation for depth 15, residue 19248. -/
theorem bounds_15_19248 : exactInterval 15 19248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19248 : oddCount 19248 15 = 6 ∧ acceleratedOrbit 15 19248 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19248) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19248.1, data_15_19248.2]

/-- Complete interval computation for depth 15, residue 19249. -/
theorem bounds_15_19249 : exactInterval 15 19249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19249 : oddCount 19249 15 = 7 ∧ acceleratedOrbit 15 19249 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19249) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19249.1, data_15_19249.2]

/-- Complete interval computation for depth 15, residue 19250. -/
theorem bounds_15_19250 : exactInterval 15 19250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19250 : oddCount 19250 15 = 7 ∧ acceleratedOrbit 15 19250 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19250) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19250.1, data_15_19250.2]

/-- Complete interval computation for depth 15, residue 19251. -/
theorem bounds_15_19251 : exactInterval 15 19251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19251 : oddCount 19251 15 = 7 ∧ acceleratedOrbit 15 19251 = 1286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19251) = 3 ^ 7 * m + 1286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19251.1, data_15_19251.2]

/-- Complete interval computation for depth 15, residue 19252. -/
theorem bounds_15_19252 : exactInterval 15 19252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19252 : oddCount 19252 15 = 6 ∧ acceleratedOrbit 15 19252 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19252) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19252.1, data_15_19252.2]

/-- Complete interval computation for depth 15, residue 19253. -/
theorem bounds_15_19253 : exactInterval 15 19253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19253 : oddCount 19253 15 = 6 ∧ acceleratedOrbit 15 19253 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19253) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19253.1, data_15_19253.2]

/-- Complete interval computation for depth 15, residue 19254. -/
theorem bounds_15_19254 : exactInterval 15 19254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19254 : oddCount 19254 15 = 8 ∧ acceleratedOrbit 15 19254 = 3856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19254) = 3 ^ 8 * m + 3856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19254.1, data_15_19254.2]

/-- Complete interval computation for depth 15, residue 19255. -/
theorem bounds_15_19255 : exactInterval 15 19255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19255 : oddCount 19255 15 = 8 ∧ acceleratedOrbit 15 19255 = 3856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19255) = 3 ^ 8 * m + 3856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19255.1, data_15_19255.2]

/-- Complete interval computation for depth 15, residue 19256. -/
theorem bounds_15_19256 : exactInterval 15 19256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19256 : oddCount 19256 15 = 9 ∧ acceleratedOrbit 15 19256 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19256) = 3 ^ 9 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19256.1, data_15_19256.2]

/-- Complete interval computation for depth 15, residue 19257. -/
theorem bounds_15_19257 : exactInterval 15 19257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19257 : oddCount 19257 15 = 10 ∧ acceleratedOrbit 15 19257 = 34708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19257) = 3 ^ 10 * m + 34708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19257.1, data_15_19257.2]

/-- Complete interval computation for depth 15, residue 19258. -/
theorem bounds_15_19258 : exactInterval 15 19258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19258 : oddCount 19258 15 = 9 ∧ acceleratedOrbit 15 19258 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19258) = 3 ^ 9 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19258.1, data_15_19258.2]

/-- Complete interval computation for depth 15, residue 19259. -/
theorem bounds_15_19259 : exactInterval 15 19259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19259 : oddCount 19259 15 = 9 ∧ acceleratedOrbit 15 19259 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19259) = 3 ^ 9 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19259.1, data_15_19259.2]

/-- Complete interval computation for depth 15, residue 19260. -/
theorem bounds_15_19260 : exactInterval 15 19260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19260 : oddCount 19260 15 = 9 ∧ acceleratedOrbit 15 19260 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19260) = 3 ^ 9 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19260.1, data_15_19260.2]

/-- Complete interval computation for depth 15, residue 19261. -/
theorem bounds_15_19261 : exactInterval 15 19261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19261 : oddCount 19261 15 = 9 ∧ acceleratedOrbit 15 19261 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19261) = 3 ^ 9 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19261.1, data_15_19261.2]

/-- Complete interval computation for depth 15, residue 19262. -/
theorem bounds_15_19262 : exactInterval 15 19262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19262 : oddCount 19262 15 = 10 ∧ acceleratedOrbit 15 19262 = 34715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19262) = 3 ^ 10 * m + 34715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19262.1, data_15_19262.2]

/-- Complete interval computation for depth 15, residue 19263. -/
theorem bounds_15_19263 : exactInterval 15 19263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19263 : oddCount 19263 15 = 10 ∧ acceleratedOrbit 15 19263 = 34715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19263) = 3 ^ 10 * m + 34715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19263.1, data_15_19263.2]

/-- Complete interval computation for depth 15, residue 19264. -/
theorem bounds_15_19264 : exactInterval 15 19264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19264 : oddCount 19264 15 = 3 ∧ acceleratedOrbit 15 19264 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19264) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19264.1, data_15_19264.2]

/-- Complete interval computation for depth 15, residue 19265. -/
theorem bounds_15_19265 : exactInterval 15 19265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19265 : oddCount 19265 15 = 6 ∧ acceleratedOrbit 15 19265 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19265) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19265.1, data_15_19265.2]

/-- Complete interval computation for depth 15, residue 19266. -/
theorem bounds_15_19266 : exactInterval 15 19266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19266 : oddCount 19266 15 = 8 ∧ acceleratedOrbit 15 19266 = 3860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19266) = 3 ^ 8 * m + 3860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19266.1, data_15_19266.2]

end Collatz.Research.PassageAtlas.Batch0588
