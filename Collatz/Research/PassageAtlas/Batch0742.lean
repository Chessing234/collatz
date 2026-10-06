import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0742

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24281. -/
theorem bounds_15_24281 : exactInterval 15 24281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24281 : oddCount 24281 15 = 7 ∧ acceleratedOrbit 15 24281 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24281) = 3 ^ 7 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24281.1, data_15_24281.2]

/-- Complete interval computation for depth 15, residue 24282. -/
theorem bounds_15_24282 : exactInterval 15 24282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24282 : oddCount 24282 15 = 7 ∧ acceleratedOrbit 15 24282 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24282) = 3 ^ 7 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24282.1, data_15_24282.2]

/-- Complete interval computation for depth 15, residue 24283. -/
theorem bounds_15_24283 : exactInterval 15 24283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24283 : oddCount 24283 15 = 9 ∧ acceleratedOrbit 15 24283 = 14588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24283) = 3 ^ 9 * m + 14588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24283.1, data_15_24283.2]

/-- Complete interval computation for depth 15, residue 24284. -/
theorem bounds_15_24284 : exactInterval 15 24284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24284 : oddCount 24284 15 = 7 ∧ acceleratedOrbit 15 24284 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24284) = 3 ^ 7 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24284.1, data_15_24284.2]

/-- Complete interval computation for depth 15, residue 24285. -/
theorem bounds_15_24285 : exactInterval 15 24285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24285 : oddCount 24285 15 = 7 ∧ acceleratedOrbit 15 24285 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24285) = 3 ^ 7 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24285.1, data_15_24285.2]

/-- Complete interval computation for depth 15, residue 24286. -/
theorem bounds_15_24286 : exactInterval 15 24286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24286 : oddCount 24286 15 = 9 ∧ acceleratedOrbit 15 24286 = 14590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24286) = 3 ^ 9 * m + 14590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24286.1, data_15_24286.2]

/-- Complete interval computation for depth 15, residue 24287. -/
theorem bounds_15_24287 : exactInterval 15 24287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24287 : oddCount 24287 15 = 9 ∧ acceleratedOrbit 15 24287 = 14590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24287) = 3 ^ 9 * m + 14590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24287.1, data_15_24287.2]

/-- Complete interval computation for depth 15, residue 24288. -/
theorem bounds_15_24288 : exactInterval 15 24288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24288 : oddCount 24288 15 = 6 ∧ acceleratedOrbit 15 24288 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24288) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24288.1, data_15_24288.2]

/-- Complete interval computation for depth 15, residue 24289. -/
theorem bounds_15_24289 : exactInterval 15 24289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24289 : oddCount 24289 15 = 8 ∧ acceleratedOrbit 15 24289 = 4864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24289) = 3 ^ 8 * m + 4864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24289.1, data_15_24289.2]

/-- Complete interval computation for depth 15, residue 24290. -/
theorem bounds_15_24290 : exactInterval 15 24290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24290 : oddCount 24290 15 = 6 ∧ acceleratedOrbit 15 24290 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24290) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24290.1, data_15_24290.2]

/-- Complete interval computation for depth 15, residue 24291. -/
theorem bounds_15_24291 : exactInterval 15 24291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24291 : oddCount 24291 15 = 6 ∧ acceleratedOrbit 15 24291 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24291) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24291.1, data_15_24291.2]

/-- Complete interval computation for depth 15, residue 24292. -/
theorem bounds_15_24292 : exactInterval 15 24292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24292 : oddCount 24292 15 = 6 ∧ acceleratedOrbit 15 24292 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24292) = 3 ^ 6 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24292.1, data_15_24292.2]

/-- Complete interval computation for depth 15, residue 24293. -/
theorem bounds_15_24293 : exactInterval 15 24293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24293 : oddCount 24293 15 = 6 ∧ acceleratedOrbit 15 24293 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24293) = 3 ^ 6 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24293.1, data_15_24293.2]

/-- Complete interval computation for depth 15, residue 24294. -/
theorem bounds_15_24294 : exactInterval 15 24294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24294 : oddCount 24294 15 = 6 ∧ acceleratedOrbit 15 24294 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24294) = 3 ^ 6 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24294.1, data_15_24294.2]

/-- Complete interval computation for depth 15, residue 24295. -/
theorem bounds_15_24295 : exactInterval 15 24295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24295 : oddCount 24295 15 = 10 ∧ acceleratedOrbit 15 24295 = 43784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24295) = 3 ^ 10 * m + 43784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24295.1, data_15_24295.2]

/-- Complete interval computation for depth 15, residue 24296. -/
theorem bounds_15_24296 : exactInterval 15 24296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24296 : oddCount 24296 15 = 6 ∧ acceleratedOrbit 15 24296 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24296) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24296.1, data_15_24296.2]

/-- Complete interval computation for depth 15, residue 24297. -/
theorem bounds_15_24297 : exactInterval 15 24297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24297 : oddCount 24297 15 = 9 ∧ acceleratedOrbit 15 24297 = 14597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24297) = 3 ^ 9 * m + 14597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24297.1, data_15_24297.2]

/-- Complete interval computation for depth 15, residue 24298. -/
theorem bounds_15_24298 : exactInterval 15 24298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24298 : oddCount 24298 15 = 6 ∧ acceleratedOrbit 15 24298 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24298) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24298.1, data_15_24298.2]

/-- Complete interval computation for depth 15, residue 24299. -/
theorem bounds_15_24299 : exactInterval 15 24299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24299 : oddCount 24299 15 = 7 ∧ acceleratedOrbit 15 24299 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24299) = 3 ^ 7 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24299.1, data_15_24299.2]

/-- Complete interval computation for depth 15, residue 24300. -/
theorem bounds_15_24300 : exactInterval 15 24300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24300 : oddCount 24300 15 = 6 ∧ acceleratedOrbit 15 24300 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24300) = 3 ^ 6 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24300.1, data_15_24300.2]

/-- Complete interval computation for depth 15, residue 24301. -/
theorem bounds_15_24301 : exactInterval 15 24301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24301 : oddCount 24301 15 = 6 ∧ acceleratedOrbit 15 24301 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24301) = 3 ^ 6 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24301.1, data_15_24301.2]

/-- Complete interval computation for depth 15, residue 24302. -/
theorem bounds_15_24302 : exactInterval 15 24302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24302 : oddCount 24302 15 = 6 ∧ acceleratedOrbit 15 24302 = 541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24302) = 3 ^ 6 * m + 541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24302.1, data_15_24302.2]

/-- Complete interval computation for depth 15, residue 24303. -/
theorem bounds_15_24303 : exactInterval 15 24303 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24303) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24303 : oddCount 24303 15 = 9 ∧ acceleratedOrbit 15 24303 = 14599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24303) = 3 ^ 9 * m + 14599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24303.1, data_15_24303.2]

/-- Complete interval computation for depth 15, residue 24304. -/
theorem bounds_15_24304 : exactInterval 15 24304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24304 : oddCount 24304 15 = 8 ∧ acceleratedOrbit 15 24304 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24304) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24304.1, data_15_24304.2]

/-- Complete interval computation for depth 15, residue 24305. -/
theorem bounds_15_24305 : exactInterval 15 24305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24305 : oddCount 24305 15 = 6 ∧ acceleratedOrbit 15 24305 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24305) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24305.1, data_15_24305.2]

/-- Complete interval computation for depth 15, residue 24306. -/
theorem bounds_15_24306 : exactInterval 15 24306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24306 : oddCount 24306 15 = 8 ∧ acceleratedOrbit 15 24306 = 4868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24306) = 3 ^ 8 * m + 4868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24306.1, data_15_24306.2]

/-- Complete interval computation for depth 15, residue 24307. -/
theorem bounds_15_24307 : exactInterval 15 24307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24307 : oddCount 24307 15 = 8 ∧ acceleratedOrbit 15 24307 = 4868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24307) = 3 ^ 8 * m + 4868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24307.1, data_15_24307.2]

/-- Complete interval computation for depth 15, residue 24308. -/
theorem bounds_15_24308 : exactInterval 15 24308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24308 : oddCount 24308 15 = 8 ∧ acceleratedOrbit 15 24308 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24308) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24308.1, data_15_24308.2]

/-- Complete interval computation for depth 15, residue 24309. -/
theorem bounds_15_24309 : exactInterval 15 24309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24309 : oddCount 24309 15 = 8 ∧ acceleratedOrbit 15 24309 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24309) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24309.1, data_15_24309.2]

/-- Complete interval computation for depth 15, residue 24310. -/
theorem bounds_15_24310 : exactInterval 15 24310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24310 : oddCount 24310 15 = 9 ∧ acceleratedOrbit 15 24310 = 14606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24310) = 3 ^ 9 * m + 14606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24310.1, data_15_24310.2]

/-- Complete interval computation for depth 15, residue 24311. -/
theorem bounds_15_24311 : exactInterval 15 24311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24311 : oddCount 24311 15 = 9 ∧ acceleratedOrbit 15 24311 = 14606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24311) = 3 ^ 9 * m + 14606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24311.1, data_15_24311.2]

/-- Complete interval computation for depth 15, residue 24312. -/
theorem bounds_15_24312 : exactInterval 15 24312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24312 : oddCount 24312 15 = 8 ∧ acceleratedOrbit 15 24312 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24312) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24312.1, data_15_24312.2]

end Collatz.Research.PassageAtlas.Batch0742
