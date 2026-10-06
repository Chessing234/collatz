import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0497

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16252. -/
theorem bounds_15_16252 : exactInterval 15 16252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16252 : oddCount 16252 15 = 7 ∧ acceleratedOrbit 15 16252 = 1085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16252) = 3 ^ 7 * m + 1085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16252.1, data_15_16252.2]

/-- Complete interval computation for depth 15, residue 16253. -/
theorem bounds_15_16253 : exactInterval 15 16253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16253 : oddCount 16253 15 = 7 ∧ acceleratedOrbit 15 16253 = 1085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16253) = 3 ^ 7 * m + 1085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16253.1, data_15_16253.2]

/-- Complete interval computation for depth 15, residue 16254. -/
theorem bounds_15_16254 : exactInterval 15 16254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16254 : oddCount 16254 15 = 11 ∧ acceleratedOrbit 15 16254 = 87884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16254) = 3 ^ 11 * m + 87884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16254.1, data_15_16254.2]

/-- Complete interval computation for depth 15, residue 16255. -/
theorem bounds_15_16255 : exactInterval 15 16255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16255 : oddCount 16255 15 = 11 ∧ acceleratedOrbit 15 16255 = 87884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16255) = 3 ^ 11 * m + 87884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16255.1, data_15_16255.2]

/-- Complete interval computation for depth 15, residue 16256. -/
theorem bounds_15_16256 : exactInterval 15 16256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16256 : oddCount 16256 15 = 7 ∧ acceleratedOrbit 15 16256 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16256) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16256.1, data_15_16256.2]

/-- Complete interval computation for depth 15, residue 16257. -/
theorem bounds_15_16257 : exactInterval 15 16257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16257 : oddCount 16257 15 = 8 ∧ acceleratedOrbit 15 16257 = 3257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16257) = 3 ^ 8 * m + 3257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16257.1, data_15_16257.2]

/-- Complete interval computation for depth 15, residue 16258. -/
theorem bounds_15_16258 : exactInterval 15 16258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16258 : oddCount 16258 15 = 6 ∧ acceleratedOrbit 15 16258 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16258) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16258.1, data_15_16258.2]

/-- Complete interval computation for depth 15, residue 16259. -/
theorem bounds_15_16259 : exactInterval 15 16259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16259 : oddCount 16259 15 = 6 ∧ acceleratedOrbit 15 16259 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16259) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16259.1, data_15_16259.2]

/-- Complete interval computation for depth 15, residue 16260. -/
theorem bounds_15_16260 : exactInterval 15 16260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16260 : oddCount 16260 15 = 10 ∧ acceleratedOrbit 15 16260 = 29321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16260) = 3 ^ 10 * m + 29321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16260.1, data_15_16260.2]

/-- Complete interval computation for depth 15, residue 16261. -/
theorem bounds_15_16261 : exactInterval 15 16261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16261 : oddCount 16261 15 = 10 ∧ acceleratedOrbit 15 16261 = 29321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16261) = 3 ^ 10 * m + 29321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16261.1, data_15_16261.2]

/-- Complete interval computation for depth 15, residue 16262. -/
theorem bounds_15_16262 : exactInterval 15 16262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16262 : oddCount 16262 15 = 10 ∧ acceleratedOrbit 15 16262 = 29321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16262) = 3 ^ 10 * m + 29321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16262.1, data_15_16262.2]

/-- Complete interval computation for depth 15, residue 16263. -/
theorem bounds_15_16263 : exactInterval 15 16263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16263 : oddCount 16263 15 = 6 ∧ acceleratedOrbit 15 16263 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16263) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16263.1, data_15_16263.2]

/-- Complete interval computation for depth 15, residue 16264. -/
theorem bounds_15_16264 : exactInterval 15 16264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16264 : oddCount 16264 15 = 6 ∧ acceleratedOrbit 15 16264 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16264) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16264.1, data_15_16264.2]

/-- Complete interval computation for depth 15, residue 16265. -/
theorem bounds_15_16265 : exactInterval 15 16265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16265 : oddCount 16265 15 = 10 ∧ acceleratedOrbit 15 16265 = 29315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16265) = 3 ^ 10 * m + 29315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16265.1, data_15_16265.2]

/-- Complete interval computation for depth 15, residue 16266. -/
theorem bounds_15_16266 : exactInterval 15 16266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16266 : oddCount 16266 15 = 6 ∧ acceleratedOrbit 15 16266 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16266) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16266.1, data_15_16266.2]

/-- Complete interval computation for depth 15, residue 16267. -/
theorem bounds_15_16267 : exactInterval 15 16267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16267 : oddCount 16267 15 = 10 ∧ acceleratedOrbit 15 16267 = 29321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16267) = 3 ^ 10 * m + 29321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16267.1, data_15_16267.2]

/-- Complete interval computation for depth 15, residue 16268. -/
theorem bounds_15_16268 : exactInterval 15 16268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16268 : oddCount 16268 15 = 6 ∧ acceleratedOrbit 15 16268 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16268) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16268.1, data_15_16268.2]

/-- Complete interval computation for depth 15, residue 16269. -/
theorem bounds_15_16269 : exactInterval 15 16269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16269 : oddCount 16269 15 = 6 ∧ acceleratedOrbit 15 16269 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16269) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16269.1, data_15_16269.2]

/-- Complete interval computation for depth 15, residue 16270. -/
theorem bounds_15_16270 : exactInterval 15 16270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16270 : oddCount 16270 15 = 9 ∧ acceleratedOrbit 15 16270 = 9776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16270) = 3 ^ 9 * m + 9776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16270.1, data_15_16270.2]

/-- Complete interval computation for depth 15, residue 16271. -/
theorem bounds_15_16271 : exactInterval 15 16271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16271 : oddCount 16271 15 = 9 ∧ acceleratedOrbit 15 16271 = 9776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16271) = 3 ^ 9 * m + 9776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16271.1, data_15_16271.2]

/-- Complete interval computation for depth 15, residue 16272. -/
theorem bounds_15_16272 : exactInterval 15 16272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16272 : oddCount 16272 15 = 8 ∧ acceleratedOrbit 15 16272 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16272) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16272.1, data_15_16272.2]

/-- Complete interval computation for depth 15, residue 16273. -/
theorem bounds_15_16273 : exactInterval 15 16273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16273 : oddCount 16273 15 = 8 ∧ acceleratedOrbit 15 16273 = 3260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16273) = 3 ^ 8 * m + 3260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16273.1, data_15_16273.2]

/-- Complete interval computation for depth 15, residue 16274. -/
theorem bounds_15_16274 : exactInterval 15 16274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16274 : oddCount 16274 15 = 8 ∧ acceleratedOrbit 15 16274 = 3260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16274) = 3 ^ 8 * m + 3260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16274.1, data_15_16274.2]

/-- Complete interval computation for depth 15, residue 16275. -/
theorem bounds_15_16275 : exactInterval 15 16275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16275 : oddCount 16275 15 = 8 ∧ acceleratedOrbit 15 16275 = 3260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16275) = 3 ^ 8 * m + 3260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16275.1, data_15_16275.2]

/-- Complete interval computation for depth 15, residue 16276. -/
theorem bounds_15_16276 : exactInterval 15 16276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16276 : oddCount 16276 15 = 8 ∧ acceleratedOrbit 15 16276 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16276) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16276.1, data_15_16276.2]

/-- Complete interval computation for depth 15, residue 16277. -/
theorem bounds_15_16277 : exactInterval 15 16277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16277 : oddCount 16277 15 = 8 ∧ acceleratedOrbit 15 16277 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16277) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16277.1, data_15_16277.2]

/-- Complete interval computation for depth 15, residue 16278. -/
theorem bounds_15_16278 : exactInterval 15 16278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16278 : oddCount 16278 15 = 5 ∧ acceleratedOrbit 15 16278 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16278) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16278.1, data_15_16278.2]

/-- Complete interval computation for depth 15, residue 16279. -/
theorem bounds_15_16279 : exactInterval 15 16279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16279 : oddCount 16279 15 = 5 ∧ acceleratedOrbit 15 16279 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16279) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16279.1, data_15_16279.2]

/-- Complete interval computation for depth 15, residue 16280. -/
theorem bounds_15_16280 : exactInterval 15 16280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16280 : oddCount 16280 15 = 8 ∧ acceleratedOrbit 15 16280 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16280) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16280.1, data_15_16280.2]

/-- Complete interval computation for depth 15, residue 16281. -/
theorem bounds_15_16281 : exactInterval 15 16281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16281 : oddCount 16281 15 = 5 ∧ acceleratedOrbit 15 16281 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16281) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16281.1, data_15_16281.2]

/-- Complete interval computation for depth 15, residue 16282. -/
theorem bounds_15_16282 : exactInterval 15 16282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16282 : oddCount 16282 15 = 8 ∧ acceleratedOrbit 15 16282 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16282) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16282.1, data_15_16282.2]

/-- Complete interval computation for depth 15, residue 16283. -/
theorem bounds_15_16283 : exactInterval 15 16283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16283 : oddCount 16283 15 = 10 ∧ acceleratedOrbit 15 16283 = 29348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16283) = 3 ^ 10 * m + 29348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16283.1, data_15_16283.2]

/-- Complete interval computation for depth 15, residue 16284. -/
theorem bounds_15_16284 : exactInterval 15 16284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16284 : oddCount 16284 15 = 8 ∧ acceleratedOrbit 15 16284 = 3262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16284) = 3 ^ 8 * m + 3262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16284.1, data_15_16284.2]

end Collatz.Research.PassageAtlas.Batch0497
