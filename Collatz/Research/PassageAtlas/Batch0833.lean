import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0833

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27262. -/
theorem bounds_15_27262 : exactInterval 15 27262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27262 : oddCount 27262 15 = 8 ∧ acceleratedOrbit 15 27262 = 5459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27262) = 3 ^ 8 * m + 5459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27262.1, data_15_27262.2]

/-- Complete interval computation for depth 15, residue 27263. -/
theorem bounds_15_27263 : exactInterval 15 27263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27263 : oddCount 27263 15 = 12 ∧ acceleratedOrbit 15 27263 = 442178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27263) = 3 ^ 12 * m + 442178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27263.1, data_15_27263.2]

/-- Complete interval computation for depth 15, residue 27264. -/
theorem bounds_15_27264 : exactInterval 15 27264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27264 : oddCount 27264 15 = 2 ∧ acceleratedOrbit 15 27264 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27264) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27264.1, data_15_27264.2]

/-- Complete interval computation for depth 15, residue 27265. -/
theorem bounds_15_27265 : exactInterval 15 27265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27265 : oddCount 27265 15 = 11 ∧ acceleratedOrbit 15 27265 = 147419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27265) = 3 ^ 11 * m + 147419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27265.1, data_15_27265.2]

/-- Complete interval computation for depth 15, residue 27266. -/
theorem bounds_15_27266 : exactInterval 15 27266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27266 : oddCount 27266 15 = 7 ∧ acceleratedOrbit 15 27266 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27266) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27266.1, data_15_27266.2]

/-- Complete interval computation for depth 15, residue 27267. -/
theorem bounds_15_27267 : exactInterval 15 27267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27267 : oddCount 27267 15 = 7 ∧ acceleratedOrbit 15 27267 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27267) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27267.1, data_15_27267.2]

/-- Complete interval computation for depth 15, residue 27268. -/
theorem bounds_15_27268 : exactInterval 15 27268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27268 : oddCount 27268 15 = 9 ∧ acceleratedOrbit 15 27268 = 16388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27268) = 3 ^ 9 * m + 16388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27268.1, data_15_27268.2]

/-- Complete interval computation for depth 15, residue 27269. -/
theorem bounds_15_27269 : exactInterval 15 27269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27269 : oddCount 27269 15 = 9 ∧ acceleratedOrbit 15 27269 = 16388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27269) = 3 ^ 9 * m + 16388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27269.1, data_15_27269.2]

/-- Complete interval computation for depth 15, residue 27270. -/
theorem bounds_15_27270 : exactInterval 15 27270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27270 : oddCount 27270 15 = 9 ∧ acceleratedOrbit 15 27270 = 16388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27270) = 3 ^ 9 * m + 16388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27270.1, data_15_27270.2]

/-- Complete interval computation for depth 15, residue 27271. -/
theorem bounds_15_27271 : exactInterval 15 27271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27271 : oddCount 27271 15 = 6 ∧ acceleratedOrbit 15 27271 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27271) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27271.1, data_15_27271.2]

/-- Complete interval computation for depth 15, residue 27272. -/
theorem bounds_15_27272 : exactInterval 15 27272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27272 : oddCount 27272 15 = 8 ∧ acceleratedOrbit 15 27272 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27272) = 3 ^ 8 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27272.1, data_15_27272.2]

/-- Complete interval computation for depth 15, residue 27273. -/
theorem bounds_15_27273 : exactInterval 15 27273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27273 : oddCount 27273 15 = 9 ∧ acceleratedOrbit 15 27273 = 16384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27273) = 3 ^ 9 * m + 16384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27273.1, data_15_27273.2]

/-- Complete interval computation for depth 15, residue 27274. -/
theorem bounds_15_27274 : exactInterval 15 27274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27274 : oddCount 27274 15 = 8 ∧ acceleratedOrbit 15 27274 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27274) = 3 ^ 8 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27274.1, data_15_27274.2]

/-- Complete interval computation for depth 15, residue 27275. -/
theorem bounds_15_27275 : exactInterval 15 27275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27275 : oddCount 27275 15 = 9 ∧ acceleratedOrbit 15 27275 = 16388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27275) = 3 ^ 9 * m + 16388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27275.1, data_15_27275.2]

/-- Complete interval computation for depth 15, residue 27276. -/
theorem bounds_15_27276 : exactInterval 15 27276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27276 : oddCount 27276 15 = 8 ∧ acceleratedOrbit 15 27276 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27276) = 3 ^ 8 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27276.1, data_15_27276.2]

/-- Complete interval computation for depth 15, residue 27277. -/
theorem bounds_15_27277 : exactInterval 15 27277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27277 : oddCount 27277 15 = 8 ∧ acceleratedOrbit 15 27277 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27277) = 3 ^ 8 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27277.1, data_15_27277.2]

/-- Complete interval computation for depth 15, residue 27278. -/
theorem bounds_15_27278 : exactInterval 15 27278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27278 : oddCount 27278 15 = 10 ∧ acceleratedOrbit 15 27278 = 49162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27278) = 3 ^ 10 * m + 49162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27278.1, data_15_27278.2]

/-- Complete interval computation for depth 15, residue 27279. -/
theorem bounds_15_27279 : exactInterval 15 27279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27279 : oddCount 27279 15 = 10 ∧ acceleratedOrbit 15 27279 = 49162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27279) = 3 ^ 10 * m + 49162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27279.1, data_15_27279.2]

/-- Complete interval computation for depth 15, residue 27280. -/
theorem bounds_15_27280 : exactInterval 15 27280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27280 : oddCount 27280 15 = 9 ∧ acceleratedOrbit 15 27280 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27280) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27280.1, data_15_27280.2]

/-- Complete interval computation for depth 15, residue 27281. -/
theorem bounds_15_27281 : exactInterval 15 27281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27281 : oddCount 27281 15 = 8 ∧ acceleratedOrbit 15 27281 = 5464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27281) = 3 ^ 8 * m + 5464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27281.1, data_15_27281.2]

/-- Complete interval computation for depth 15, residue 27282. -/
theorem bounds_15_27282 : exactInterval 15 27282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27282 : oddCount 27282 15 = 8 ∧ acceleratedOrbit 15 27282 = 5464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27282) = 3 ^ 8 * m + 5464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27282.1, data_15_27282.2]

/-- Complete interval computation for depth 15, residue 27283. -/
theorem bounds_15_27283 : exactInterval 15 27283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27283 : oddCount 27283 15 = 8 ∧ acceleratedOrbit 15 27283 = 5464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27283) = 3 ^ 8 * m + 5464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27283.1, data_15_27283.2]

/-- Complete interval computation for depth 15, residue 27284. -/
theorem bounds_15_27284 : exactInterval 15 27284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27284 : oddCount 27284 15 = 9 ∧ acceleratedOrbit 15 27284 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27284) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27284.1, data_15_27284.2]

/-- Complete interval computation for depth 15, residue 27285. -/
theorem bounds_15_27285 : exactInterval 15 27285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27285 : oddCount 27285 15 = 9 ∧ acceleratedOrbit 15 27285 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27285) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27285.1, data_15_27285.2]

/-- Complete interval computation for depth 15, residue 27286. -/
theorem bounds_15_27286 : exactInterval 15 27286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27286 : oddCount 27286 15 = 8 ∧ acceleratedOrbit 15 27286 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27286) = 3 ^ 8 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27286.1, data_15_27286.2]

/-- Complete interval computation for depth 15, residue 27287. -/
theorem bounds_15_27287 : exactInterval 15 27287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27287 : oddCount 27287 15 = 8 ∧ acceleratedOrbit 15 27287 = 5467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27287) = 3 ^ 8 * m + 5467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27287.1, data_15_27287.2]

/-- Complete interval computation for depth 15, residue 27288. -/
theorem bounds_15_27288 : exactInterval 15 27288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27288 : oddCount 27288 15 = 9 ∧ acceleratedOrbit 15 27288 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27288) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27288.1, data_15_27288.2]

/-- Complete interval computation for depth 15, residue 27289. -/
theorem bounds_15_27289 : exactInterval 15 27289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27289 : oddCount 27289 15 = 8 ∧ acceleratedOrbit 15 27289 = 5465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27289) = 3 ^ 8 * m + 5465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27289.1, data_15_27289.2]

/-- Complete interval computation for depth 15, residue 27290. -/
theorem bounds_15_27290 : exactInterval 15 27290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27290 : oddCount 27290 15 = 9 ∧ acceleratedOrbit 15 27290 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27290) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27290.1, data_15_27290.2]

/-- Complete interval computation for depth 15, residue 27291. -/
theorem bounds_15_27291 : exactInterval 15 27291 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27291) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27291 : oddCount 27291 15 = 9 ∧ acceleratedOrbit 15 27291 = 16394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27291) = 3 ^ 9 * m + 16394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27291.1, data_15_27291.2]

/-- Complete interval computation for depth 15, residue 27292. -/
theorem bounds_15_27292 : exactInterval 15 27292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27292 : oddCount 27292 15 = 10 ∧ acceleratedOrbit 15 27292 = 49193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27292) = 3 ^ 10 * m + 49193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27292.1, data_15_27292.2]

/-- Complete interval computation for depth 15, residue 27293. -/
theorem bounds_15_27293 : exactInterval 15 27293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27293 : oddCount 27293 15 = 10 ∧ acceleratedOrbit 15 27293 = 49193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27293) = 3 ^ 10 * m + 49193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27293.1, data_15_27293.2]

/-- Complete interval computation for depth 15, residue 27294. -/
theorem bounds_15_27294 : exactInterval 15 27294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27294 : oddCount 27294 15 = 10 ∧ acceleratedOrbit 15 27294 = 49193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27294) = 3 ^ 10 * m + 49193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27294.1, data_15_27294.2]

end Collatz.Research.PassageAtlas.Batch0833
