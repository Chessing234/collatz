import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0314

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10256. -/
theorem bounds_15_10256 : exactInterval 15 10256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10256 : oddCount 10256 15 = 7 ∧ acceleratedOrbit 15 10256 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10256) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10256.1, data_15_10256.2]

/-- Complete interval computation for depth 15, residue 10257. -/
theorem bounds_15_10257 : exactInterval 15 10257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10257 : oddCount 10257 15 = 6 ∧ acceleratedOrbit 15 10257 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10257) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10257.1, data_15_10257.2]

/-- Complete interval computation for depth 15, residue 10258. -/
theorem bounds_15_10258 : exactInterval 15 10258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10258 : oddCount 10258 15 = 7 ∧ acceleratedOrbit 15 10258 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10258) = 3 ^ 7 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10258.1, data_15_10258.2]

/-- Complete interval computation for depth 15, residue 10259. -/
theorem bounds_15_10259 : exactInterval 15 10259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10259 : oddCount 10259 15 = 7 ∧ acceleratedOrbit 15 10259 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10259) = 3 ^ 7 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10259.1, data_15_10259.2]

/-- Complete interval computation for depth 15, residue 10260. -/
theorem bounds_15_10260 : exactInterval 15 10260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10260 : oddCount 10260 15 = 7 ∧ acceleratedOrbit 15 10260 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10260) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10260.1, data_15_10260.2]

/-- Complete interval computation for depth 15, residue 10261. -/
theorem bounds_15_10261 : exactInterval 15 10261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10261 : oddCount 10261 15 = 7 ∧ acceleratedOrbit 15 10261 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10261) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10261.1, data_15_10261.2]

/-- Complete interval computation for depth 15, residue 10262. -/
theorem bounds_15_10262 : exactInterval 15 10262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10262 : oddCount 10262 15 = 6 ∧ acceleratedOrbit 15 10262 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10262) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10262.1, data_15_10262.2]

/-- Complete interval computation for depth 15, residue 10263. -/
theorem bounds_15_10263 : exactInterval 15 10263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10263 : oddCount 10263 15 = 6 ∧ acceleratedOrbit 15 10263 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10263) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10263.1, data_15_10263.2]

/-- Complete interval computation for depth 15, residue 10264. -/
theorem bounds_15_10264 : exactInterval 15 10264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10264 : oddCount 10264 15 = 7 ∧ acceleratedOrbit 15 10264 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10264) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10264.1, data_15_10264.2]

/-- Complete interval computation for depth 15, residue 10265. -/
theorem bounds_15_10265 : exactInterval 15 10265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10265 : oddCount 10265 15 = 9 ∧ acceleratedOrbit 15 10265 = 6169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10265) = 3 ^ 9 * m + 6169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10265.1, data_15_10265.2]

/-- Complete interval computation for depth 15, residue 10266. -/
theorem bounds_15_10266 : exactInterval 15 10266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10266 : oddCount 10266 15 = 7 ∧ acceleratedOrbit 15 10266 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10266) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10266.1, data_15_10266.2]

/-- Complete interval computation for depth 15, residue 10267. -/
theorem bounds_15_10267 : exactInterval 15 10267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10267 : oddCount 10267 15 = 8 ∧ acceleratedOrbit 15 10267 = 2056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10267) = 3 ^ 8 * m + 2056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10267.1, data_15_10267.2]

/-- Complete interval computation for depth 15, residue 10268. -/
theorem bounds_15_10268 : exactInterval 15 10268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10268 : oddCount 10268 15 = 7 ∧ acceleratedOrbit 15 10268 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10268) = 3 ^ 7 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10268.1, data_15_10268.2]

/-- Complete interval computation for depth 15, residue 10269. -/
theorem bounds_15_10269 : exactInterval 15 10269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10269 : oddCount 10269 15 = 7 ∧ acceleratedOrbit 15 10269 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10269) = 3 ^ 7 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10269.1, data_15_10269.2]

/-- Complete interval computation for depth 15, residue 10270. -/
theorem bounds_15_10270 : exactInterval 15 10270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10270 : oddCount 10270 15 = 7 ∧ acceleratedOrbit 15 10270 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10270) = 3 ^ 7 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10270.1, data_15_10270.2]

/-- Complete interval computation for depth 15, residue 10271. -/
theorem bounds_15_10271 : exactInterval 15 10271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10271 : oddCount 10271 15 = 10 ∧ acceleratedOrbit 15 10271 = 18512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10271) = 3 ^ 10 * m + 18512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10271.1, data_15_10271.2]

/-- Complete interval computation for depth 15, residue 10272. -/
theorem bounds_15_10272 : exactInterval 15 10272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10272 : oddCount 10272 15 = 4 ∧ acceleratedOrbit 15 10272 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10272) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10272.1, data_15_10272.2]

/-- Complete interval computation for depth 15, residue 10273. -/
theorem bounds_15_10273 : exactInterval 15 10273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10273 : oddCount 10273 15 = 7 ∧ acceleratedOrbit 15 10273 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10273) = 3 ^ 7 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10273.1, data_15_10273.2]

/-- Complete interval computation for depth 15, residue 10274. -/
theorem bounds_15_10274 : exactInterval 15 10274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10274 : oddCount 10274 15 = 7 ∧ acceleratedOrbit 15 10274 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10274) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10274.1, data_15_10274.2]

/-- Complete interval computation for depth 15, residue 10275. -/
theorem bounds_15_10275 : exactInterval 15 10275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10275 : oddCount 10275 15 = 7 ∧ acceleratedOrbit 15 10275 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10275) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10275.1, data_15_10275.2]

/-- Complete interval computation for depth 15, residue 10276. -/
theorem bounds_15_10276 : exactInterval 15 10276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10276 : oddCount 10276 15 = 6 ∧ acceleratedOrbit 15 10276 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10276) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10276.1, data_15_10276.2]

/-- Complete interval computation for depth 15, residue 10277. -/
theorem bounds_15_10277 : exactInterval 15 10277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10277 : oddCount 10277 15 = 6 ∧ acceleratedOrbit 15 10277 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10277) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10277.1, data_15_10277.2]

/-- Complete interval computation for depth 15, residue 10278. -/
theorem bounds_15_10278 : exactInterval 15 10278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10278 : oddCount 10278 15 = 6 ∧ acceleratedOrbit 15 10278 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10278) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10278.1, data_15_10278.2]

/-- Complete interval computation for depth 15, residue 10279. -/
theorem bounds_15_10279 : exactInterval 15 10279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10279 : oddCount 10279 15 = 9 ∧ acceleratedOrbit 15 10279 = 6176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10279) = 3 ^ 9 * m + 6176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10279.1, data_15_10279.2]

/-- Complete interval computation for depth 15, residue 10280. -/
theorem bounds_15_10280 : exactInterval 15 10280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10280 : oddCount 10280 15 = 4 ∧ acceleratedOrbit 15 10280 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10280) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10280.1, data_15_10280.2]

/-- Complete interval computation for depth 15, residue 10281. -/
theorem bounds_15_10281 : exactInterval 15 10281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10281 : oddCount 10281 15 = 11 ∧ acceleratedOrbit 15 10281 = 55592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10281) = 3 ^ 11 * m + 55592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10281.1, data_15_10281.2]

/-- Complete interval computation for depth 15, residue 10282. -/
theorem bounds_15_10282 : exactInterval 15 10282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10282 : oddCount 10282 15 = 4 ∧ acceleratedOrbit 15 10282 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10282) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10282.1, data_15_10282.2]

/-- Complete interval computation for depth 15, residue 10283. -/
theorem bounds_15_10283 : exactInterval 15 10283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10283 : oddCount 10283 15 = 9 ∧ acceleratedOrbit 15 10283 = 6182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10283) = 3 ^ 9 * m + 6182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10283.1, data_15_10283.2]

/-- Complete interval computation for depth 15, residue 10284. -/
theorem bounds_15_10284 : exactInterval 15 10284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10284 : oddCount 10284 15 = 7 ∧ acceleratedOrbit 15 10284 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10284) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10284.1, data_15_10284.2]

/-- Complete interval computation for depth 15, residue 10285. -/
theorem bounds_15_10285 : exactInterval 15 10285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10285 : oddCount 10285 15 = 7 ∧ acceleratedOrbit 15 10285 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10285) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10285.1, data_15_10285.2]

/-- Complete interval computation for depth 15, residue 10286. -/
theorem bounds_15_10286 : exactInterval 15 10286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10286 : oddCount 10286 15 = 7 ∧ acceleratedOrbit 15 10286 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10286) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10286.1, data_15_10286.2]

/-- Complete interval computation for depth 15, residue 10287. -/
theorem bounds_15_10287 : exactInterval 15 10287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10287 : oddCount 10287 15 = 8 ∧ acceleratedOrbit 15 10287 = 2060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10287) = 3 ^ 8 * m + 2060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10287.1, data_15_10287.2]

/-- Complete interval computation for depth 15, residue 10288. -/
theorem bounds_15_10288 : exactInterval 15 10288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10288 : oddCount 10288 15 = 4 ∧ acceleratedOrbit 15 10288 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10288) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10288.1, data_15_10288.2]

end Collatz.Research.PassageAtlas.Batch0314
