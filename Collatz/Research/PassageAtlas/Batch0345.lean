import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0345

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11272. -/
theorem bounds_15_11272 : exactInterval 15 11272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11272 : oddCount 11272 15 = 7 ∧ acceleratedOrbit 15 11272 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11272) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11272.1, data_15_11272.2]

/-- Complete interval computation for depth 15, residue 11273. -/
theorem bounds_15_11273 : exactInterval 15 11273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11273 : oddCount 11273 15 = 10 ∧ acceleratedOrbit 15 11273 = 20321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11273) = 3 ^ 10 * m + 20321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11273.1, data_15_11273.2]

/-- Complete interval computation for depth 15, residue 11274. -/
theorem bounds_15_11274 : exactInterval 15 11274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11274 : oddCount 11274 15 = 7 ∧ acceleratedOrbit 15 11274 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11274) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11274.1, data_15_11274.2]

/-- Complete interval computation for depth 15, residue 11275. -/
theorem bounds_15_11275 : exactInterval 15 11275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11275 : oddCount 11275 15 = 7 ∧ acceleratedOrbit 15 11275 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11275) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11275.1, data_15_11275.2]

/-- Complete interval computation for depth 15, residue 11276. -/
theorem bounds_15_11276 : exactInterval 15 11276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11276 : oddCount 11276 15 = 7 ∧ acceleratedOrbit 15 11276 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11276) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11276.1, data_15_11276.2]

/-- Complete interval computation for depth 15, residue 11277. -/
theorem bounds_15_11277 : exactInterval 15 11277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11277 : oddCount 11277 15 = 7 ∧ acceleratedOrbit 15 11277 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11277) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11277.1, data_15_11277.2]

/-- Complete interval computation for depth 15, residue 11278. -/
theorem bounds_15_11278 : exactInterval 15 11278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11278 : oddCount 11278 15 = 6 ∧ acceleratedOrbit 15 11278 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11278) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11278.1, data_15_11278.2]

/-- Complete interval computation for depth 15, residue 11279. -/
theorem bounds_15_11279 : exactInterval 15 11279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11279 : oddCount 11279 15 = 6 ∧ acceleratedOrbit 15 11279 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11279) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11279.1, data_15_11279.2]

/-- Complete interval computation for depth 15, residue 11280. -/
theorem bounds_15_11280 : exactInterval 15 11280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11280 : oddCount 11280 15 = 4 ∧ acceleratedOrbit 15 11280 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11280) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11280.1, data_15_11280.2]

/-- Complete interval computation for depth 15, residue 11281. -/
theorem bounds_15_11281 : exactInterval 15 11281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11281 : oddCount 11281 15 = 7 ∧ acceleratedOrbit 15 11281 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11281) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11281.1, data_15_11281.2]

/-- Complete interval computation for depth 15, residue 11282. -/
theorem bounds_15_11282 : exactInterval 15 11282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11282 : oddCount 11282 15 = 8 ∧ acceleratedOrbit 15 11282 = 2261 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11282) = 3 ^ 8 * m + 2261 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11282.1, data_15_11282.2]

/-- Complete interval computation for depth 15, residue 11283. -/
theorem bounds_15_11283 : exactInterval 15 11283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11283 : oddCount 11283 15 = 8 ∧ acceleratedOrbit 15 11283 = 2261 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11283) = 3 ^ 8 * m + 2261 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11283.1, data_15_11283.2]

/-- Complete interval computation for depth 15, residue 11284. -/
theorem bounds_15_11284 : exactInterval 15 11284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11284 : oddCount 11284 15 = 4 ∧ acceleratedOrbit 15 11284 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11284) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11284.1, data_15_11284.2]

/-- Complete interval computation for depth 15, residue 11285. -/
theorem bounds_15_11285 : exactInterval 15 11285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11285 : oddCount 11285 15 = 4 ∧ acceleratedOrbit 15 11285 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11285) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11285.1, data_15_11285.2]

/-- Complete interval computation for depth 15, residue 11286. -/
theorem bounds_15_11286 : exactInterval 15 11286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11286 : oddCount 11286 15 = 7 ∧ acceleratedOrbit 15 11286 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11286) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11286.1, data_15_11286.2]

/-- Complete interval computation for depth 15, residue 11287. -/
theorem bounds_15_11287 : exactInterval 15 11287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11287 : oddCount 11287 15 = 7 ∧ acceleratedOrbit 15 11287 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11287) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11287.1, data_15_11287.2]

/-- Complete interval computation for depth 15, residue 11288. -/
theorem bounds_15_11288 : exactInterval 15 11288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11288 : oddCount 11288 15 = 4 ∧ acceleratedOrbit 15 11288 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11288) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11288.1, data_15_11288.2]

/-- Complete interval computation for depth 15, residue 11289. -/
theorem bounds_15_11289 : exactInterval 15 11289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11289 : oddCount 11289 15 = 10 ∧ acceleratedOrbit 15 11289 = 20351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11289) = 3 ^ 10 * m + 20351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11289.1, data_15_11289.2]

/-- Complete interval computation for depth 15, residue 11290. -/
theorem bounds_15_11290 : exactInterval 15 11290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11290 : oddCount 11290 15 = 4 ∧ acceleratedOrbit 15 11290 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11290) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11290.1, data_15_11290.2]

/-- Complete interval computation for depth 15, residue 11291. -/
theorem bounds_15_11291 : exactInterval 15 11291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11291 : oddCount 11291 15 = 11 ∧ acceleratedOrbit 15 11291 = 61049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11291) = 3 ^ 11 * m + 61049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11291.1, data_15_11291.2]

/-- Complete interval computation for depth 15, residue 11292. -/
theorem bounds_15_11292 : exactInterval 15 11292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11292 : oddCount 11292 15 = 8 ∧ acceleratedOrbit 15 11292 = 2263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11292) = 3 ^ 8 * m + 2263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11292.1, data_15_11292.2]

/-- Complete interval computation for depth 15, residue 11293. -/
theorem bounds_15_11293 : exactInterval 15 11293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11293 : oddCount 11293 15 = 8 ∧ acceleratedOrbit 15 11293 = 2263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11293) = 3 ^ 8 * m + 2263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11293.1, data_15_11293.2]

/-- Complete interval computation for depth 15, residue 11294. -/
theorem bounds_15_11294 : exactInterval 15 11294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11294 : oddCount 11294 15 = 8 ∧ acceleratedOrbit 15 11294 = 2263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11294) = 3 ^ 8 * m + 2263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11294.1, data_15_11294.2]

/-- Complete interval computation for depth 15, residue 11295. -/
theorem bounds_15_11295 : exactInterval 15 11295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11295 : oddCount 11295 15 = 11 ∧ acceleratedOrbit 15 11295 = 61069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11295) = 3 ^ 11 * m + 61069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11295.1, data_15_11295.2]

/-- Complete interval computation for depth 15, residue 11296. -/
theorem bounds_15_11296 : exactInterval 15 11296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11296 : oddCount 11296 15 = 6 ∧ acceleratedOrbit 15 11296 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11296) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11296.1, data_15_11296.2]

/-- Complete interval computation for depth 15, residue 11297. -/
theorem bounds_15_11297 : exactInterval 15 11297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11297 : oddCount 11297 15 = 8 ∧ acceleratedOrbit 15 11297 = 2263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11297) = 3 ^ 8 * m + 2263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11297.1, data_15_11297.2]

/-- Complete interval computation for depth 15, residue 11298. -/
theorem bounds_15_11298 : exactInterval 15 11298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11298 : oddCount 11298 15 = 4 ∧ acceleratedOrbit 15 11298 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11298) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11298.1, data_15_11298.2]

/-- Complete interval computation for depth 15, residue 11299. -/
theorem bounds_15_11299 : exactInterval 15 11299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11299 : oddCount 11299 15 = 4 ∧ acceleratedOrbit 15 11299 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11299) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11299.1, data_15_11299.2]

/-- Complete interval computation for depth 15, residue 11300. -/
theorem bounds_15_11300 : exactInterval 15 11300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11300 : oddCount 11300 15 = 9 ∧ acceleratedOrbit 15 11300 = 6794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11300) = 3 ^ 9 * m + 6794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11300.1, data_15_11300.2]

/-- Complete interval computation for depth 15, residue 11301. -/
theorem bounds_15_11301 : exactInterval 15 11301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11301 : oddCount 11301 15 = 9 ∧ acceleratedOrbit 15 11301 = 6794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11301) = 3 ^ 9 * m + 6794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11301.1, data_15_11301.2]

/-- Complete interval computation for depth 15, residue 11302. -/
theorem bounds_15_11302 : exactInterval 15 11302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11302 : oddCount 11302 15 = 9 ∧ acceleratedOrbit 15 11302 = 6794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11302) = 3 ^ 9 * m + 6794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11302.1, data_15_11302.2]

/-- Complete interval computation for depth 15, residue 11303. -/
theorem bounds_15_11303 : exactInterval 15 11303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11303 : oddCount 11303 15 = 7 ∧ acceleratedOrbit 15 11303 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11303) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11303.1, data_15_11303.2]

end Collatz.Research.PassageAtlas.Batch0345
