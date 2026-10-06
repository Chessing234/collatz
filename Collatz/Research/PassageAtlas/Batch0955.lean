import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0955

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31260. -/
theorem bounds_15_31260 : exactInterval 15 31260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31260 : oddCount 31260 15 = 8 ∧ acceleratedOrbit 15 31260 = 6263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31260) = 3 ^ 8 * m + 6263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31260.1, data_15_31260.2]

/-- Complete interval computation for depth 15, residue 31261. -/
theorem bounds_15_31261 : exactInterval 15 31261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31261 : oddCount 31261 15 = 8 ∧ acceleratedOrbit 15 31261 = 6263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31261) = 3 ^ 8 * m + 6263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31261.1, data_15_31261.2]

/-- Complete interval computation for depth 15, residue 31262. -/
theorem bounds_15_31262 : exactInterval 15 31262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31262 : oddCount 31262 15 = 8 ∧ acceleratedOrbit 15 31262 = 6263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31262) = 3 ^ 8 * m + 6263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31262.1, data_15_31262.2]

/-- Complete interval computation for depth 15, residue 31263. -/
theorem bounds_15_31263 : exactInterval 15 31263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31263 : oddCount 31263 15 = 8 ∧ acceleratedOrbit 15 31263 = 6260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31263) = 3 ^ 8 * m + 6260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31263.1, data_15_31263.2]

/-- Complete interval computation for depth 15, residue 31264. -/
theorem bounds_15_31264 : exactInterval 15 31264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31264 : oddCount 31264 15 = 5 ∧ acceleratedOrbit 15 31264 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31264) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31264.1, data_15_31264.2]

/-- Complete interval computation for depth 15, residue 31265. -/
theorem bounds_15_31265 : exactInterval 15 31265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31265 : oddCount 31265 15 = 8 ∧ acceleratedOrbit 15 31265 = 6263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31265) = 3 ^ 8 * m + 6263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31265.1, data_15_31265.2]

/-- Complete interval computation for depth 15, residue 31266. -/
theorem bounds_15_31266 : exactInterval 15 31266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31266 : oddCount 31266 15 = 5 ∧ acceleratedOrbit 15 31266 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31266) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31266.1, data_15_31266.2]

/-- Complete interval computation for depth 15, residue 31267. -/
theorem bounds_15_31267 : exactInterval 15 31267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31267 : oddCount 31267 15 = 5 ∧ acceleratedOrbit 15 31267 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31267) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31267.1, data_15_31267.2]

/-- Complete interval computation for depth 15, residue 31268. -/
theorem bounds_15_31268 : exactInterval 15 31268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31268 : oddCount 31268 15 = 9 ∧ acceleratedOrbit 15 31268 = 18787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31268) = 3 ^ 9 * m + 18787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31268.1, data_15_31268.2]

/-- Complete interval computation for depth 15, residue 31269. -/
theorem bounds_15_31269 : exactInterval 15 31269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31269 : oddCount 31269 15 = 9 ∧ acceleratedOrbit 15 31269 = 18787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31269) = 3 ^ 9 * m + 18787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31269.1, data_15_31269.2]

/-- Complete interval computation for depth 15, residue 31270. -/
theorem bounds_15_31270 : exactInterval 15 31270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31270 : oddCount 31270 15 = 9 ∧ acceleratedOrbit 15 31270 = 18787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31270) = 3 ^ 9 * m + 18787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31270.1, data_15_31270.2]

/-- Complete interval computation for depth 15, residue 31271. -/
theorem bounds_15_31271 : exactInterval 15 31271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31271 : oddCount 31271 15 = 8 ∧ acceleratedOrbit 15 31271 = 6263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31271) = 3 ^ 8 * m + 6263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31271.1, data_15_31271.2]

/-- Complete interval computation for depth 15, residue 31272. -/
theorem bounds_15_31272 : exactInterval 15 31272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31272 : oddCount 31272 15 = 5 ∧ acceleratedOrbit 15 31272 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31272) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31272.1, data_15_31272.2]

/-- Complete interval computation for depth 15, residue 31273. -/
theorem bounds_15_31273 : exactInterval 15 31273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31273 : oddCount 31273 15 = 8 ∧ acceleratedOrbit 15 31273 = 6262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31273) = 3 ^ 8 * m + 6262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31273.1, data_15_31273.2]

/-- Complete interval computation for depth 15, residue 31274. -/
theorem bounds_15_31274 : exactInterval 15 31274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31274 : oddCount 31274 15 = 5 ∧ acceleratedOrbit 15 31274 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31274) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31274.1, data_15_31274.2]

/-- Complete interval computation for depth 15, residue 31275. -/
theorem bounds_15_31275 : exactInterval 15 31275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31275 : oddCount 31275 15 = 5 ∧ acceleratedOrbit 15 31275 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31275) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31275.1, data_15_31275.2]

/-- Complete interval computation for depth 15, residue 31276. -/
theorem bounds_15_31276 : exactInterval 15 31276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31276 : oddCount 31276 15 = 5 ∧ acceleratedOrbit 15 31276 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31276) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31276.1, data_15_31276.2]

/-- Complete interval computation for depth 15, residue 31277. -/
theorem bounds_15_31277 : exactInterval 15 31277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31277 : oddCount 31277 15 = 5 ∧ acceleratedOrbit 15 31277 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31277) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31277.1, data_15_31277.2]

/-- Complete interval computation for depth 15, residue 31278. -/
theorem bounds_15_31278 : exactInterval 15 31278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31278 : oddCount 31278 15 = 5 ∧ acceleratedOrbit 15 31278 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31278) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31278.1, data_15_31278.2]

/-- Complete interval computation for depth 15, residue 31279. -/
theorem bounds_15_31279 : exactInterval 15 31279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31279 : oddCount 31279 15 = 10 ∧ acceleratedOrbit 15 31279 = 56369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31279) = 3 ^ 10 * m + 56369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31279.1, data_15_31279.2]

/-- Complete interval computation for depth 15, residue 31280. -/
theorem bounds_15_31280 : exactInterval 15 31280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31280 : oddCount 31280 15 = 5 ∧ acceleratedOrbit 15 31280 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31280) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31280.1, data_15_31280.2]

/-- Complete interval computation for depth 15, residue 31281. -/
theorem bounds_15_31281 : exactInterval 15 31281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31281 : oddCount 31281 15 = 8 ∧ acceleratedOrbit 15 31281 = 6265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31281) = 3 ^ 8 * m + 6265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31281.1, data_15_31281.2]

/-- Complete interval computation for depth 15, residue 31282. -/
theorem bounds_15_31282 : exactInterval 15 31282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31282 : oddCount 31282 15 = 8 ∧ acceleratedOrbit 15 31282 = 6265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31282) = 3 ^ 8 * m + 6265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31282.1, data_15_31282.2]

/-- Complete interval computation for depth 15, residue 31283. -/
theorem bounds_15_31283 : exactInterval 15 31283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31283 : oddCount 31283 15 = 8 ∧ acceleratedOrbit 15 31283 = 6265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31283) = 3 ^ 8 * m + 6265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31283.1, data_15_31283.2]

/-- Complete interval computation for depth 15, residue 31284. -/
theorem bounds_15_31284 : exactInterval 15 31284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31284 : oddCount 31284 15 = 5 ∧ acceleratedOrbit 15 31284 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31284) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31284.1, data_15_31284.2]

/-- Complete interval computation for depth 15, residue 31285. -/
theorem bounds_15_31285 : exactInterval 15 31285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31285 : oddCount 31285 15 = 5 ∧ acceleratedOrbit 15 31285 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31285) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31285.1, data_15_31285.2]

/-- Complete interval computation for depth 15, residue 31286. -/
theorem bounds_15_31286 : exactInterval 15 31286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31286 : oddCount 31286 15 = 10 ∧ acceleratedOrbit 15 31286 = 56384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31286) = 3 ^ 10 * m + 56384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31286.1, data_15_31286.2]

/-- Complete interval computation for depth 15, residue 31287. -/
theorem bounds_15_31287 : exactInterval 15 31287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31287 : oddCount 31287 15 = 10 ∧ acceleratedOrbit 15 31287 = 56384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31287) = 3 ^ 10 * m + 56384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31287.1, data_15_31287.2]

/-- Complete interval computation for depth 15, residue 31288. -/
theorem bounds_15_31288 : exactInterval 15 31288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31288 : oddCount 31288 15 = 7 ∧ acceleratedOrbit 15 31288 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31288) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31288.1, data_15_31288.2]

/-- Complete interval computation for depth 15, residue 31289. -/
theorem bounds_15_31289 : exactInterval 15 31289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31289 : oddCount 31289 15 = 8 ∧ acceleratedOrbit 15 31289 = 6266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31289) = 3 ^ 8 * m + 6266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31289.1, data_15_31289.2]

/-- Complete interval computation for depth 15, residue 31290. -/
theorem bounds_15_31290 : exactInterval 15 31290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31290 : oddCount 31290 15 = 7 ∧ acceleratedOrbit 15 31290 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31290) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31290.1, data_15_31290.2]

/-- Complete interval computation for depth 15, residue 31291. -/
theorem bounds_15_31291 : exactInterval 15 31291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31291 : oddCount 31291 15 = 7 ∧ acceleratedOrbit 15 31291 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31291) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31291.1, data_15_31291.2]

/-- Complete interval computation for depth 15, residue 31292. -/
theorem bounds_15_31292 : exactInterval 15 31292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31292 : oddCount 31292 15 = 7 ∧ acceleratedOrbit 15 31292 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31292) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31292.1, data_15_31292.2]

end Collatz.Research.PassageAtlas.Batch0955
