import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0527

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17235. -/
theorem bounds_15_17235 : exactInterval 15 17235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17235 : oddCount 17235 15 = 10 ∧ acceleratedOrbit 15 17235 = 31063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17235) = 3 ^ 10 * m + 31063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17235.1, data_15_17235.2]

/-- Complete interval computation for depth 15, residue 17236. -/
theorem bounds_15_17236 : exactInterval 15 17236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17236 : oddCount 17236 15 = 4 ∧ acceleratedOrbit 15 17236 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17236) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17236.1, data_15_17236.2]

/-- Complete interval computation for depth 15, residue 17237. -/
theorem bounds_15_17237 : exactInterval 15 17237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17237 : oddCount 17237 15 = 4 ∧ acceleratedOrbit 15 17237 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17237) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17237.1, data_15_17237.2]

/-- Complete interval computation for depth 15, residue 17238. -/
theorem bounds_15_17238 : exactInterval 15 17238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17238 : oddCount 17238 15 = 9 ∧ acceleratedOrbit 15 17238 = 10358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17238) = 3 ^ 9 * m + 10358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17238.1, data_15_17238.2]

/-- Complete interval computation for depth 15, residue 17239. -/
theorem bounds_15_17239 : exactInterval 15 17239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17239 : oddCount 17239 15 = 9 ∧ acceleratedOrbit 15 17239 = 10358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17239) = 3 ^ 9 * m + 10358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17239.1, data_15_17239.2]

/-- Complete interval computation for depth 15, residue 17240. -/
theorem bounds_15_17240 : exactInterval 15 17240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17240 : oddCount 17240 15 = 9 ∧ acceleratedOrbit 15 17240 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17240) = 3 ^ 9 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17240.1, data_15_17240.2]

/-- Complete interval computation for depth 15, residue 17241. -/
theorem bounds_15_17241 : exactInterval 15 17241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17241 : oddCount 17241 15 = 5 ∧ acceleratedOrbit 15 17241 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17241) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17241.1, data_15_17241.2]

/-- Complete interval computation for depth 15, residue 17242. -/
theorem bounds_15_17242 : exactInterval 15 17242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17242 : oddCount 17242 15 = 9 ∧ acceleratedOrbit 15 17242 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17242) = 3 ^ 9 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17242.1, data_15_17242.2]

/-- Complete interval computation for depth 15, residue 17243. -/
theorem bounds_15_17243 : exactInterval 15 17243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17243 : oddCount 17243 15 = 11 ∧ acceleratedOrbit 15 17243 = 93230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17243) = 3 ^ 11 * m + 93230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17243.1, data_15_17243.2]

/-- Complete interval computation for depth 15, residue 17244. -/
theorem bounds_15_17244 : exactInterval 15 17244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17244 : oddCount 17244 15 = 9 ∧ acceleratedOrbit 15 17244 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17244) = 3 ^ 9 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17244.1, data_15_17244.2]

/-- Complete interval computation for depth 15, residue 17245. -/
theorem bounds_15_17245 : exactInterval 15 17245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17245 : oddCount 17245 15 = 9 ∧ acceleratedOrbit 15 17245 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17245) = 3 ^ 9 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17245.1, data_15_17245.2]

/-- Complete interval computation for depth 15, residue 17246. -/
theorem bounds_15_17246 : exactInterval 15 17246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17246 : oddCount 17246 15 = 8 ∧ acceleratedOrbit 15 17246 = 3455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17246) = 3 ^ 8 * m + 3455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17246.1, data_15_17246.2]

/-- Complete interval computation for depth 15, residue 17247. -/
theorem bounds_15_17247 : exactInterval 15 17247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17247 : oddCount 17247 15 = 8 ∧ acceleratedOrbit 15 17247 = 3455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17247) = 3 ^ 8 * m + 3455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17247.1, data_15_17247.2]

/-- Complete interval computation for depth 15, residue 17248. -/
theorem bounds_15_17248 : exactInterval 15 17248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17248 : oddCount 17248 15 = 7 ∧ acceleratedOrbit 15 17248 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17248) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17248.1, data_15_17248.2]

/-- Complete interval computation for depth 15, residue 17249. -/
theorem bounds_15_17249 : exactInterval 15 17249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17249 : oddCount 17249 15 = 9 ∧ acceleratedOrbit 15 17249 = 10363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17249) = 3 ^ 9 * m + 10363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17249.1, data_15_17249.2]

/-- Complete interval computation for depth 15, residue 17250. -/
theorem bounds_15_17250 : exactInterval 15 17250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17250 : oddCount 17250 15 = 7 ∧ acceleratedOrbit 15 17250 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17250) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17250.1, data_15_17250.2]

/-- Complete interval computation for depth 15, residue 17251. -/
theorem bounds_15_17251 : exactInterval 15 17251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17251 : oddCount 17251 15 = 7 ∧ acceleratedOrbit 15 17251 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17251) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17251.1, data_15_17251.2]

/-- Complete interval computation for depth 15, residue 17252. -/
theorem bounds_15_17252 : exactInterval 15 17252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17252 : oddCount 17252 15 = 7 ∧ acceleratedOrbit 15 17252 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17252) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17252.1, data_15_17252.2]

/-- Complete interval computation for depth 15, residue 17253. -/
theorem bounds_15_17253 : exactInterval 15 17253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17253 : oddCount 17253 15 = 7 ∧ acceleratedOrbit 15 17253 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17253) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17253.1, data_15_17253.2]

/-- Complete interval computation for depth 15, residue 17254. -/
theorem bounds_15_17254 : exactInterval 15 17254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17254 : oddCount 17254 15 = 7 ∧ acceleratedOrbit 15 17254 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17254) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17254.1, data_15_17254.2]

/-- Complete interval computation for depth 15, residue 17255. -/
theorem bounds_15_17255 : exactInterval 15 17255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17255 : oddCount 17255 15 = 12 ∧ acceleratedOrbit 15 17255 = 279868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17255) = 3 ^ 12 * m + 279868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17255.1, data_15_17255.2]

/-- Complete interval computation for depth 15, residue 17256. -/
theorem bounds_15_17256 : exactInterval 15 17256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17256 : oddCount 17256 15 = 7 ∧ acceleratedOrbit 15 17256 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17256) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17256.1, data_15_17256.2]

/-- Complete interval computation for depth 15, residue 17257. -/
theorem bounds_15_17257 : exactInterval 15 17257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17257 : oddCount 17257 15 = 11 ∧ acceleratedOrbit 15 17257 = 93311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17257) = 3 ^ 11 * m + 93311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17257.1, data_15_17257.2]

/-- Complete interval computation for depth 15, residue 17258. -/
theorem bounds_15_17258 : exactInterval 15 17258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17258 : oddCount 17258 15 = 7 ∧ acceleratedOrbit 15 17258 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17258) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17258.1, data_15_17258.2]

/-- Complete interval computation for depth 15, residue 17259. -/
theorem bounds_15_17259 : exactInterval 15 17259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17259 : oddCount 17259 15 = 5 ∧ acceleratedOrbit 15 17259 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17259) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17259.1, data_15_17259.2]

/-- Complete interval computation for depth 15, residue 17260. -/
theorem bounds_15_17260 : exactInterval 15 17260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17260 : oddCount 17260 15 = 8 ∧ acceleratedOrbit 15 17260 = 3458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17260) = 3 ^ 8 * m + 3458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17260.1, data_15_17260.2]

/-- Complete interval computation for depth 15, residue 17261. -/
theorem bounds_15_17261 : exactInterval 15 17261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17261 : oddCount 17261 15 = 8 ∧ acceleratedOrbit 15 17261 = 3458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17261) = 3 ^ 8 * m + 3458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17261.1, data_15_17261.2]

/-- Complete interval computation for depth 15, residue 17262. -/
theorem bounds_15_17262 : exactInterval 15 17262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17262 : oddCount 17262 15 = 8 ∧ acceleratedOrbit 15 17262 = 3458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17262) = 3 ^ 8 * m + 3458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17262.1, data_15_17262.2]

/-- Complete interval computation for depth 15, residue 17263. -/
theorem bounds_15_17263 : exactInterval 15 17263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17263 : oddCount 17263 15 = 8 ∧ acceleratedOrbit 15 17263 = 3457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17263) = 3 ^ 8 * m + 3457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17263.1, data_15_17263.2]

/-- Complete interval computation for depth 15, residue 17264. -/
theorem bounds_15_17264 : exactInterval 15 17264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17264 : oddCount 17264 15 = 7 ∧ acceleratedOrbit 15 17264 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17264) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17264.1, data_15_17264.2]

/-- Complete interval computation for depth 15, residue 17265. -/
theorem bounds_15_17265 : exactInterval 15 17265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17265 : oddCount 17265 15 = 7 ∧ acceleratedOrbit 15 17265 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17265) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17265.1, data_15_17265.2]

/-- Complete interval computation for depth 15, residue 17266. -/
theorem bounds_15_17266 : exactInterval 15 17266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17266 : oddCount 17266 15 = 7 ∧ acceleratedOrbit 15 17266 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17266) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17266.1, data_15_17266.2]

/-- Complete interval computation for depth 15, residue 17267. -/
theorem bounds_15_17267 : exactInterval 15 17267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17267 : oddCount 17267 15 = 7 ∧ acceleratedOrbit 15 17267 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17267) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17267.1, data_15_17267.2]

end Collatz.Research.PassageAtlas.Batch0527
