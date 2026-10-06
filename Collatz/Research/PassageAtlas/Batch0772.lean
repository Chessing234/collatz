import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0772

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25264. -/
theorem bounds_15_25264 : exactInterval 15 25264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25264 : oddCount 25264 15 = 5 ∧ acceleratedOrbit 15 25264 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25264) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25264.1, data_15_25264.2]

/-- Complete interval computation for depth 15, residue 25265. -/
theorem bounds_15_25265 : exactInterval 15 25265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25265 : oddCount 25265 15 = 8 ∧ acceleratedOrbit 15 25265 = 5062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25265) = 3 ^ 8 * m + 5062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25265.1, data_15_25265.2]

/-- Complete interval computation for depth 15, residue 25266. -/
theorem bounds_15_25266 : exactInterval 15 25266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25266 : oddCount 25266 15 = 8 ∧ acceleratedOrbit 15 25266 = 5062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25266) = 3 ^ 8 * m + 5062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25266.1, data_15_25266.2]

/-- Complete interval computation for depth 15, residue 25267. -/
theorem bounds_15_25267 : exactInterval 15 25267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25267 : oddCount 25267 15 = 8 ∧ acceleratedOrbit 15 25267 = 5062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25267) = 3 ^ 8 * m + 5062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25267.1, data_15_25267.2]

/-- Complete interval computation for depth 15, residue 25268. -/
theorem bounds_15_25268 : exactInterval 15 25268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25268 : oddCount 25268 15 = 5 ∧ acceleratedOrbit 15 25268 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25268) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25268.1, data_15_25268.2]

/-- Complete interval computation for depth 15, residue 25269. -/
theorem bounds_15_25269 : exactInterval 15 25269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25269 : oddCount 25269 15 = 5 ∧ acceleratedOrbit 15 25269 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25269) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25269.1, data_15_25269.2]

/-- Complete interval computation for depth 15, residue 25270. -/
theorem bounds_15_25270 : exactInterval 15 25270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25270 : oddCount 25270 15 = 7 ∧ acceleratedOrbit 15 25270 = 1687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25270) = 3 ^ 7 * m + 1687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25270.1, data_15_25270.2]

/-- Complete interval computation for depth 15, residue 25271. -/
theorem bounds_15_25271 : exactInterval 15 25271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25271 : oddCount 25271 15 = 7 ∧ acceleratedOrbit 15 25271 = 1687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25271) = 3 ^ 7 * m + 1687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25271.1, data_15_25271.2]

/-- Complete interval computation for depth 15, residue 25272. -/
theorem bounds_15_25272 : exactInterval 15 25272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25272 : oddCount 25272 15 = 5 ∧ acceleratedOrbit 15 25272 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25272) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25272.1, data_15_25272.2]

/-- Complete interval computation for depth 15, residue 25273. -/
theorem bounds_15_25273 : exactInterval 15 25273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25273 : oddCount 25273 15 = 8 ∧ acceleratedOrbit 15 25273 = 5062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25273) = 3 ^ 8 * m + 5062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25273.1, data_15_25273.2]

/-- Complete interval computation for depth 15, residue 25274. -/
theorem bounds_15_25274 : exactInterval 15 25274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25274 : oddCount 25274 15 = 5 ∧ acceleratedOrbit 15 25274 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25274) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25274.1, data_15_25274.2]

/-- Complete interval computation for depth 15, residue 25275. -/
theorem bounds_15_25275 : exactInterval 15 25275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25275 : oddCount 25275 15 = 9 ∧ acceleratedOrbit 15 25275 = 15184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25275) = 3 ^ 9 * m + 15184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25275.1, data_15_25275.2]

/-- Complete interval computation for depth 15, residue 25276. -/
theorem bounds_15_25276 : exactInterval 15 25276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25276 : oddCount 25276 15 = 9 ∧ acceleratedOrbit 15 25276 = 15187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25276) = 3 ^ 9 * m + 15187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25276.1, data_15_25276.2]

/-- Complete interval computation for depth 15, residue 25277. -/
theorem bounds_15_25277 : exactInterval 15 25277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25277 : oddCount 25277 15 = 9 ∧ acceleratedOrbit 15 25277 = 15187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25277) = 3 ^ 9 * m + 15187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25277.1, data_15_25277.2]

/-- Complete interval computation for depth 15, residue 25278. -/
theorem bounds_15_25278 : exactInterval 15 25278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25278 : oddCount 25278 15 = 9 ∧ acceleratedOrbit 15 25278 = 15187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25278) = 3 ^ 9 * m + 15187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25278.1, data_15_25278.2]

/-- Complete interval computation for depth 15, residue 25279. -/
theorem bounds_15_25279 : exactInterval 15 25279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25279 : oddCount 25279 15 = 11 ∧ acceleratedOrbit 15 25279 = 136667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25279) = 3 ^ 11 * m + 136667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25279.1, data_15_25279.2]

/-- Complete interval computation for depth 15, residue 25280. -/
theorem bounds_15_25280 : exactInterval 15 25280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25280 : oddCount 25280 15 = 6 ∧ acceleratedOrbit 15 25280 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25280) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25280.1, data_15_25280.2]

/-- Complete interval computation for depth 15, residue 25281. -/
theorem bounds_15_25281 : exactInterval 15 25281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25281 : oddCount 25281 15 = 5 ∧ acceleratedOrbit 15 25281 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25281) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25281.1, data_15_25281.2]

/-- Complete interval computation for depth 15, residue 25282. -/
theorem bounds_15_25282 : exactInterval 15 25282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25282 : oddCount 25282 15 = 9 ∧ acceleratedOrbit 15 25282 = 15191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25282) = 3 ^ 9 * m + 15191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25282.1, data_15_25282.2]

/-- Complete interval computation for depth 15, residue 25283. -/
theorem bounds_15_25283 : exactInterval 15 25283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25283 : oddCount 25283 15 = 9 ∧ acceleratedOrbit 15 25283 = 15191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25283) = 3 ^ 9 * m + 15191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25283.1, data_15_25283.2]

/-- Complete interval computation for depth 15, residue 25284. -/
theorem bounds_15_25284 : exactInterval 15 25284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25284 : oddCount 25284 15 = 7 ∧ acceleratedOrbit 15 25284 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25284) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25284.1, data_15_25284.2]

/-- Complete interval computation for depth 15, residue 25285. -/
theorem bounds_15_25285 : exactInterval 15 25285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25285 : oddCount 25285 15 = 7 ∧ acceleratedOrbit 15 25285 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25285) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25285.1, data_15_25285.2]

/-- Complete interval computation for depth 15, residue 25286. -/
theorem bounds_15_25286 : exactInterval 15 25286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25286 : oddCount 25286 15 = 7 ∧ acceleratedOrbit 15 25286 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25286) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25286.1, data_15_25286.2]

/-- Complete interval computation for depth 15, residue 25287. -/
theorem bounds_15_25287 : exactInterval 15 25287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25287 : oddCount 25287 15 = 7 ∧ acceleratedOrbit 15 25287 = 1688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25287) = 3 ^ 7 * m + 1688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25287.1, data_15_25287.2]

/-- Complete interval computation for depth 15, residue 25288. -/
theorem bounds_15_25288 : exactInterval 15 25288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25288 : oddCount 25288 15 = 7 ∧ acceleratedOrbit 15 25288 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25288) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25288.1, data_15_25288.2]

/-- Complete interval computation for depth 15, residue 25289. -/
theorem bounds_15_25289 : exactInterval 15 25289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25289 : oddCount 25289 15 = 8 ∧ acceleratedOrbit 15 25289 = 5066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25289) = 3 ^ 8 * m + 5066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25289.1, data_15_25289.2]

/-- Complete interval computation for depth 15, residue 25290. -/
theorem bounds_15_25290 : exactInterval 15 25290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25290 : oddCount 25290 15 = 7 ∧ acceleratedOrbit 15 25290 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25290) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25290.1, data_15_25290.2]

/-- Complete interval computation for depth 15, residue 25291. -/
theorem bounds_15_25291 : exactInterval 15 25291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25291 : oddCount 25291 15 = 8 ∧ acceleratedOrbit 15 25291 = 5066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25291) = 3 ^ 8 * m + 5066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25291.1, data_15_25291.2]

/-- Complete interval computation for depth 15, residue 25292. -/
theorem bounds_15_25292 : exactInterval 15 25292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25292 : oddCount 25292 15 = 7 ∧ acceleratedOrbit 15 25292 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25292) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25292.1, data_15_25292.2]

/-- Complete interval computation for depth 15, residue 25293. -/
theorem bounds_15_25293 : exactInterval 15 25293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25293 : oddCount 25293 15 = 7 ∧ acceleratedOrbit 15 25293 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25293) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25293.1, data_15_25293.2]

/-- Complete interval computation for depth 15, residue 25294. -/
theorem bounds_15_25294 : exactInterval 15 25294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25294 : oddCount 25294 15 = 8 ∧ acceleratedOrbit 15 25294 = 5065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25294) = 3 ^ 8 * m + 5065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25294.1, data_15_25294.2]

/-- Complete interval computation for depth 15, residue 25295. -/
theorem bounds_15_25295 : exactInterval 15 25295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25295 : oddCount 25295 15 = 8 ∧ acceleratedOrbit 15 25295 = 5065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25295) = 3 ^ 8 * m + 5065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25295.1, data_15_25295.2]

end Collatz.Research.PassageAtlas.Batch0772
