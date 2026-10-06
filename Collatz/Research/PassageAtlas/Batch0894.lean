import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0894

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29261. -/
theorem bounds_15_29261 : exactInterval 15 29261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29261 : oddCount 29261 15 = 7 ∧ acceleratedOrbit 15 29261 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29261) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29261.1, data_15_29261.2]

/-- Complete interval computation for depth 15, residue 29262. -/
theorem bounds_15_29262 : exactInterval 15 29262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29262 : oddCount 29262 15 = 8 ∧ acceleratedOrbit 15 29262 = 5860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29262) = 3 ^ 8 * m + 5860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29262.1, data_15_29262.2]

/-- Complete interval computation for depth 15, residue 29263. -/
theorem bounds_15_29263 : exactInterval 15 29263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29263 : oddCount 29263 15 = 8 ∧ acceleratedOrbit 15 29263 = 5860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29263) = 3 ^ 8 * m + 5860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29263.1, data_15_29263.2]

/-- Complete interval computation for depth 15, residue 29264. -/
theorem bounds_15_29264 : exactInterval 15 29264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29264 : oddCount 29264 15 = 5 ∧ acceleratedOrbit 15 29264 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29264) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29264.1, data_15_29264.2]

/-- Complete interval computation for depth 15, residue 29265. -/
theorem bounds_15_29265 : exactInterval 15 29265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29265 : oddCount 29265 15 = 8 ∧ acceleratedOrbit 15 29265 = 5861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29265) = 3 ^ 8 * m + 5861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29265.1, data_15_29265.2]

/-- Complete interval computation for depth 15, residue 29266. -/
theorem bounds_15_29266 : exactInterval 15 29266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29266 : oddCount 29266 15 = 8 ∧ acceleratedOrbit 15 29266 = 5861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29266) = 3 ^ 8 * m + 5861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29266.1, data_15_29266.2]

/-- Complete interval computation for depth 15, residue 29267. -/
theorem bounds_15_29267 : exactInterval 15 29267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29267 : oddCount 29267 15 = 8 ∧ acceleratedOrbit 15 29267 = 5861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29267) = 3 ^ 8 * m + 5861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29267.1, data_15_29267.2]

/-- Complete interval computation for depth 15, residue 29268. -/
theorem bounds_15_29268 : exactInterval 15 29268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29268 : oddCount 29268 15 = 5 ∧ acceleratedOrbit 15 29268 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29268) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29268.1, data_15_29268.2]

/-- Complete interval computation for depth 15, residue 29269. -/
theorem bounds_15_29269 : exactInterval 15 29269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29269 : oddCount 29269 15 = 5 ∧ acceleratedOrbit 15 29269 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29269) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29269.1, data_15_29269.2]

/-- Complete interval computation for depth 15, residue 29270. -/
theorem bounds_15_29270 : exactInterval 15 29270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29270 : oddCount 29270 15 = 7 ∧ acceleratedOrbit 15 29270 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29270) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29270.1, data_15_29270.2]

/-- Complete interval computation for depth 15, residue 29271. -/
theorem bounds_15_29271 : exactInterval 15 29271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29271 : oddCount 29271 15 = 7 ∧ acceleratedOrbit 15 29271 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29271) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29271.1, data_15_29271.2]

/-- Complete interval computation for depth 15, residue 29272. -/
theorem bounds_15_29272 : exactInterval 15 29272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29272 : oddCount 29272 15 = 5 ∧ acceleratedOrbit 15 29272 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29272) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29272.1, data_15_29272.2]

/-- Complete interval computation for depth 15, residue 29273. -/
theorem bounds_15_29273 : exactInterval 15 29273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29273 : oddCount 29273 15 = 9 ∧ acceleratedOrbit 15 29273 = 17587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29273) = 3 ^ 9 * m + 17587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29273.1, data_15_29273.2]

/-- Complete interval computation for depth 15, residue 29274. -/
theorem bounds_15_29274 : exactInterval 15 29274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29274 : oddCount 29274 15 = 5 ∧ acceleratedOrbit 15 29274 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29274) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29274.1, data_15_29274.2]

/-- Complete interval computation for depth 15, residue 29275. -/
theorem bounds_15_29275 : exactInterval 15 29275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29275 : oddCount 29275 15 = 12 ∧ acceleratedOrbit 15 29275 = 474821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29275) = 3 ^ 12 * m + 474821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29275.1, data_15_29275.2]

/-- Complete interval computation for depth 15, residue 29276. -/
theorem bounds_15_29276 : exactInterval 15 29276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29276 : oddCount 29276 15 = 5 ∧ acceleratedOrbit 15 29276 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29276) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29276.1, data_15_29276.2]

/-- Complete interval computation for depth 15, residue 29277. -/
theorem bounds_15_29277 : exactInterval 15 29277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29277 : oddCount 29277 15 = 5 ∧ acceleratedOrbit 15 29277 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29277) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29277.1, data_15_29277.2]

/-- Complete interval computation for depth 15, residue 29278. -/
theorem bounds_15_29278 : exactInterval 15 29278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29278 : oddCount 29278 15 = 8 ∧ acceleratedOrbit 15 29278 = 5863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29278) = 3 ^ 8 * m + 5863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29278.1, data_15_29278.2]

/-- Complete interval computation for depth 15, residue 29279. -/
theorem bounds_15_29279 : exactInterval 15 29279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29279 : oddCount 29279 15 = 8 ∧ acceleratedOrbit 15 29279 = 5863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29279) = 3 ^ 8 * m + 5863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29279.1, data_15_29279.2]

/-- Complete interval computation for depth 15, residue 29280. -/
theorem bounds_15_29280 : exactInterval 15 29280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29280 : oddCount 29280 15 = 5 ∧ acceleratedOrbit 15 29280 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29280) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29280.1, data_15_29280.2]

/-- Complete interval computation for depth 15, residue 29281. -/
theorem bounds_15_29281 : exactInterval 15 29281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29281 : oddCount 29281 15 = 7 ∧ acceleratedOrbit 15 29281 = 1955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29281) = 3 ^ 7 * m + 1955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29281.1, data_15_29281.2]

/-- Complete interval computation for depth 15, residue 29282. -/
theorem bounds_15_29282 : exactInterval 15 29282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29282 : oddCount 29282 15 = 6 ∧ acceleratedOrbit 15 29282 = 652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29282) = 3 ^ 6 * m + 652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29282.1, data_15_29282.2]

/-- Complete interval computation for depth 15, residue 29283. -/
theorem bounds_15_29283 : exactInterval 15 29283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29283 : oddCount 29283 15 = 6 ∧ acceleratedOrbit 15 29283 = 652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29283) = 3 ^ 6 * m + 652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29283.1, data_15_29283.2]

/-- Complete interval computation for depth 15, residue 29284. -/
theorem bounds_15_29284 : exactInterval 15 29284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29284 : oddCount 29284 15 = 6 ∧ acceleratedOrbit 15 29284 = 652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29284) = 3 ^ 6 * m + 652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29284.1, data_15_29284.2]

/-- Complete interval computation for depth 15, residue 29285. -/
theorem bounds_15_29285 : exactInterval 15 29285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29285 : oddCount 29285 15 = 6 ∧ acceleratedOrbit 15 29285 = 652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29285) = 3 ^ 6 * m + 652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29285.1, data_15_29285.2]

/-- Complete interval computation for depth 15, residue 29286. -/
theorem bounds_15_29286 : exactInterval 15 29286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29286 : oddCount 29286 15 = 6 ∧ acceleratedOrbit 15 29286 = 652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29286) = 3 ^ 6 * m + 652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29286.1, data_15_29286.2]

/-- Complete interval computation for depth 15, residue 29287. -/
theorem bounds_15_29287 : exactInterval 15 29287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29287 : oddCount 29287 15 = 9 ∧ acceleratedOrbit 15 29287 = 17594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29287) = 3 ^ 9 * m + 17594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29287.1, data_15_29287.2]

/-- Complete interval computation for depth 15, residue 29288. -/
theorem bounds_15_29288 : exactInterval 15 29288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29288 : oddCount 29288 15 = 5 ∧ acceleratedOrbit 15 29288 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29288) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29288.1, data_15_29288.2]

/-- Complete interval computation for depth 15, residue 29289. -/
theorem bounds_15_29289 : exactInterval 15 29289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29289 : oddCount 29289 15 = 11 ∧ acceleratedOrbit 15 29289 = 158354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29289) = 3 ^ 11 * m + 158354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29289.1, data_15_29289.2]

/-- Complete interval computation for depth 15, residue 29290. -/
theorem bounds_15_29290 : exactInterval 15 29290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29290 : oddCount 29290 15 = 5 ∧ acceleratedOrbit 15 29290 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29290) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29290.1, data_15_29290.2]

/-- Complete interval computation for depth 15, residue 29291. -/
theorem bounds_15_29291 : exactInterval 15 29291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29291 : oddCount 29291 15 = 9 ∧ acceleratedOrbit 15 29291 = 17597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29291) = 3 ^ 9 * m + 17597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29291.1, data_15_29291.2]

/-- Complete interval computation for depth 15, residue 29292. -/
theorem bounds_15_29292 : exactInterval 15 29292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29292 : oddCount 29292 15 = 9 ∧ acceleratedOrbit 15 29292 = 17599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29292) = 3 ^ 9 * m + 17599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29292.1, data_15_29292.2]

/-- Complete interval computation for depth 15, residue 29293. -/
theorem bounds_15_29293 : exactInterval 15 29293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29293 : oddCount 29293 15 = 9 ∧ acceleratedOrbit 15 29293 = 17599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29293) = 3 ^ 9 * m + 17599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29293.1, data_15_29293.2]

end Collatz.Research.PassageAtlas.Batch0894
