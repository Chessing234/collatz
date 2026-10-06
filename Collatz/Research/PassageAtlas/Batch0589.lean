import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0589

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19267. -/
theorem bounds_15_19267 : exactInterval 15 19267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19267 : oddCount 19267 15 = 8 ∧ acceleratedOrbit 15 19267 = 3860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19267) = 3 ^ 8 * m + 3860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19267.1, data_15_19267.2]

/-- Complete interval computation for depth 15, residue 19268. -/
theorem bounds_15_19268 : exactInterval 15 19268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19268 : oddCount 19268 15 = 5 ∧ acceleratedOrbit 15 19268 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19268) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19268.1, data_15_19268.2]

/-- Complete interval computation for depth 15, residue 19269. -/
theorem bounds_15_19269 : exactInterval 15 19269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19269 : oddCount 19269 15 = 5 ∧ acceleratedOrbit 15 19269 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19269) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19269.1, data_15_19269.2]

/-- Complete interval computation for depth 15, residue 19270. -/
theorem bounds_15_19270 : exactInterval 15 19270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19270 : oddCount 19270 15 = 5 ∧ acceleratedOrbit 15 19270 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19270) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19270.1, data_15_19270.2]

/-- Complete interval computation for depth 15, residue 19271. -/
theorem bounds_15_19271 : exactInterval 15 19271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19271 : oddCount 19271 15 = 11 ∧ acceleratedOrbit 15 19271 = 104192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19271) = 3 ^ 11 * m + 104192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19271.1, data_15_19271.2]

/-- Complete interval computation for depth 15, residue 19272. -/
theorem bounds_15_19272 : exactInterval 15 19272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19272 : oddCount 19272 15 = 5 ∧ acceleratedOrbit 15 19272 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19272) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19272.1, data_15_19272.2]

/-- Complete interval computation for depth 15, residue 19273. -/
theorem bounds_15_19273 : exactInterval 15 19273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19273 : oddCount 19273 15 = 9 ∧ acceleratedOrbit 15 19273 = 11582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19273) = 3 ^ 9 * m + 11582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19273.1, data_15_19273.2]

/-- Complete interval computation for depth 15, residue 19274. -/
theorem bounds_15_19274 : exactInterval 15 19274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19274 : oddCount 19274 15 = 5 ∧ acceleratedOrbit 15 19274 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19274) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19274.1, data_15_19274.2]

/-- Complete interval computation for depth 15, residue 19275. -/
theorem bounds_15_19275 : exactInterval 15 19275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19275 : oddCount 19275 15 = 5 ∧ acceleratedOrbit 15 19275 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19275) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19275.1, data_15_19275.2]

/-- Complete interval computation for depth 15, residue 19276. -/
theorem bounds_15_19276 : exactInterval 15 19276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19276 : oddCount 19276 15 = 5 ∧ acceleratedOrbit 15 19276 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19276) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19276.1, data_15_19276.2]

/-- Complete interval computation for depth 15, residue 19277. -/
theorem bounds_15_19277 : exactInterval 15 19277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19277 : oddCount 19277 15 = 5 ∧ acceleratedOrbit 15 19277 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19277) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19277.1, data_15_19277.2]

/-- Complete interval computation for depth 15, residue 19278. -/
theorem bounds_15_19278 : exactInterval 15 19278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19278 : oddCount 19278 15 = 10 ∧ acceleratedOrbit 15 19278 = 34748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19278) = 3 ^ 10 * m + 34748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19278.1, data_15_19278.2]

/-- Complete interval computation for depth 15, residue 19279. -/
theorem bounds_15_19279 : exactInterval 15 19279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19279 : oddCount 19279 15 = 10 ∧ acceleratedOrbit 15 19279 = 34748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19279) = 3 ^ 10 * m + 34748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19279.1, data_15_19279.2]

/-- Complete interval computation for depth 15, residue 19280. -/
theorem bounds_15_19280 : exactInterval 15 19280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19280 : oddCount 19280 15 = 3 ∧ acceleratedOrbit 15 19280 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19280) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19280.1, data_15_19280.2]

/-- Complete interval computation for depth 15, residue 19281. -/
theorem bounds_15_19281 : exactInterval 15 19281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19281 : oddCount 19281 15 = 9 ∧ acceleratedOrbit 15 19281 = 11585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19281) = 3 ^ 9 * m + 11585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19281.1, data_15_19281.2]

/-- Complete interval computation for depth 15, residue 19282. -/
theorem bounds_15_19282 : exactInterval 15 19282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19282 : oddCount 19282 15 = 9 ∧ acceleratedOrbit 15 19282 = 11585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19282) = 3 ^ 9 * m + 11585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19282.1, data_15_19282.2]

/-- Complete interval computation for depth 15, residue 19283. -/
theorem bounds_15_19283 : exactInterval 15 19283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19283 : oddCount 19283 15 = 9 ∧ acceleratedOrbit 15 19283 = 11585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19283) = 3 ^ 9 * m + 11585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19283.1, data_15_19283.2]

/-- Complete interval computation for depth 15, residue 19284. -/
theorem bounds_15_19284 : exactInterval 15 19284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19284 : oddCount 19284 15 = 3 ∧ acceleratedOrbit 15 19284 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19284) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19284.1, data_15_19284.2]

/-- Complete interval computation for depth 15, residue 19285. -/
theorem bounds_15_19285 : exactInterval 15 19285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19285 : oddCount 19285 15 = 3 ∧ acceleratedOrbit 15 19285 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19285) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19285.1, data_15_19285.2]

/-- Complete interval computation for depth 15, residue 19286. -/
theorem bounds_15_19286 : exactInterval 15 19286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19286 : oddCount 19286 15 = 8 ∧ acceleratedOrbit 15 19286 = 3863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19286) = 3 ^ 8 * m + 3863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19286.1, data_15_19286.2]

/-- Complete interval computation for depth 15, residue 19287. -/
theorem bounds_15_19287 : exactInterval 15 19287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19287 : oddCount 19287 15 = 8 ∧ acceleratedOrbit 15 19287 = 3863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19287) = 3 ^ 8 * m + 3863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19287.1, data_15_19287.2]

/-- Complete interval computation for depth 15, residue 19288. -/
theorem bounds_15_19288 : exactInterval 15 19288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19288 : oddCount 19288 15 = 7 ∧ acceleratedOrbit 15 19288 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19288) = 3 ^ 7 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19288.1, data_15_19288.2]

/-- Complete interval computation for depth 15, residue 19289. -/
theorem bounds_15_19289 : exactInterval 15 19289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19289 : oddCount 19289 15 = 7 ∧ acceleratedOrbit 15 19289 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19289) = 3 ^ 7 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19289.1, data_15_19289.2]

/-- Complete interval computation for depth 15, residue 19290. -/
theorem bounds_15_19290 : exactInterval 15 19290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19290 : oddCount 19290 15 = 7 ∧ acceleratedOrbit 15 19290 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19290) = 3 ^ 7 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19290.1, data_15_19290.2]

/-- Complete interval computation for depth 15, residue 19291. -/
theorem bounds_15_19291 : exactInterval 15 19291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19291 : oddCount 19291 15 = 8 ∧ acceleratedOrbit 15 19291 = 3863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19291) = 3 ^ 8 * m + 3863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19291.1, data_15_19291.2]

/-- Complete interval computation for depth 15, residue 19292. -/
theorem bounds_15_19292 : exactInterval 15 19292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19292 : oddCount 19292 15 = 7 ∧ acceleratedOrbit 15 19292 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19292) = 3 ^ 7 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19292.1, data_15_19292.2]

/-- Complete interval computation for depth 15, residue 19293. -/
theorem bounds_15_19293 : exactInterval 15 19293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19293 : oddCount 19293 15 = 7 ∧ acceleratedOrbit 15 19293 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19293) = 3 ^ 7 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19293.1, data_15_19293.2]

/-- Complete interval computation for depth 15, residue 19294. -/
theorem bounds_15_19294 : exactInterval 15 19294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19294 : oddCount 19294 15 = 7 ∧ acceleratedOrbit 15 19294 = 1288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19294) = 3 ^ 7 * m + 1288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19294.1, data_15_19294.2]

/-- Complete interval computation for depth 15, residue 19295. -/
theorem bounds_15_19295 : exactInterval 15 19295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19295 : oddCount 19295 15 = 7 ∧ acceleratedOrbit 15 19295 = 1288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19295) = 3 ^ 7 * m + 1288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19295.1, data_15_19295.2]

/-- Complete interval computation for depth 15, residue 19296. -/
theorem bounds_15_19296 : exactInterval 15 19296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19296 : oddCount 19296 15 = 7 ∧ acceleratedOrbit 15 19296 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19296) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19296.1, data_15_19296.2]

/-- Complete interval computation for depth 15, residue 19297. -/
theorem bounds_15_19297 : exactInterval 15 19297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19297 : oddCount 19297 15 = 9 ∧ acceleratedOrbit 15 19297 = 11593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19297) = 3 ^ 9 * m + 11593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19297.1, data_15_19297.2]

/-- Complete interval computation for depth 15, residue 19298. -/
theorem bounds_15_19298 : exactInterval 15 19298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19298 : oddCount 19298 15 = 6 ∧ acceleratedOrbit 15 19298 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19298) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19298.1, data_15_19298.2]

/-- Complete interval computation for depth 15, residue 19299. -/
theorem bounds_15_19299 : exactInterval 15 19299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19299 : oddCount 19299 15 = 6 ∧ acceleratedOrbit 15 19299 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19299) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19299.1, data_15_19299.2]

end Collatz.Research.PassageAtlas.Batch0589
