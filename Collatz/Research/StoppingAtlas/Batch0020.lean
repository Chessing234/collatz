import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0020

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 291. -/
theorem bounds_10_291 : exactInterval 10 291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_291 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 291) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_291 : oddCount 291 10 = 5 ∧ acceleratedOrbit 10 291 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_291 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 291) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_291.1, data_10_291.2]

/-- Complete interval computation for depth 10, residue 292. -/
theorem bounds_10_292 : exactInterval 10 292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_292 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 292) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_292 : oddCount 292 10 = 5 ∧ acceleratedOrbit 10 292 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_292 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 292) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_292.1, data_10_292.2]

/-- Complete interval computation for depth 10, residue 293. -/
theorem bounds_10_293 : exactInterval 10 293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_293 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 293) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_293 : oddCount 293 10 = 5 ∧ acceleratedOrbit 10 293 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_293 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 293) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_293.1, data_10_293.2]

/-- Complete interval computation for depth 10, residue 294. -/
theorem bounds_10_294 : exactInterval 10 294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_294 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 294) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_294 : oddCount 294 10 = 5 ∧ acceleratedOrbit 10 294 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_294 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 294) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_294.1, data_10_294.2]

/-- Complete interval computation for depth 10, residue 295. -/
theorem bounds_10_295 : exactInterval 10 295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_295 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 295) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_295 : oddCount 295 10 = 6 ∧ acceleratedOrbit 10 295 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_295 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 295) = 3 ^ 6 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_295.1, data_10_295.2]

/-- Complete interval computation for depth 10, residue 296. -/
theorem bounds_10_296 : exactInterval 10 296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_296 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 296) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_296 : oddCount 296 10 = 4 ∧ acceleratedOrbit 10 296 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_296 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 296) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_296.1, data_10_296.2]

/-- Complete interval computation for depth 10, residue 297. -/
theorem bounds_10_297 : exactInterval 10 297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_297 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 297) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_297 : oddCount 297 10 = 7 ∧ acceleratedOrbit 10 297 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_297 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 297) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_297.1, data_10_297.2]

/-- Complete interval computation for depth 10, residue 298. -/
theorem bounds_10_298 : exactInterval 10 298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_298 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 298) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_298 : oddCount 298 10 = 4 ∧ acceleratedOrbit 10 298 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_298 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 298) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_298.1, data_10_298.2]

/-- Complete interval computation for depth 10, residue 299. -/
theorem bounds_10_299 : exactInterval 10 299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_299 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 299) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_299 : oddCount 299 10 = 6 ∧ acceleratedOrbit 10 299 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_299 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 299) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_299.1, data_10_299.2]

/-- Complete interval computation for depth 10, residue 300. -/
theorem bounds_10_300 : exactInterval 10 300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_300 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 300) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_300 : oddCount 300 10 = 3 ∧ acceleratedOrbit 10 300 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_300 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 300) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_300.1, data_10_300.2]

/-- Complete interval computation for depth 10, residue 301. -/
theorem bounds_10_301 : exactInterval 10 301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_301 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 301) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_301 : oddCount 301 10 = 3 ∧ acceleratedOrbit 10 301 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_301 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 301) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_301.1, data_10_301.2]

/-- Complete interval computation for depth 10, residue 302. -/
theorem bounds_10_302 : exactInterval 10 302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_302 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 302) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_302 : oddCount 302 10 = 3 ∧ acceleratedOrbit 10 302 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_302 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 302) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_302.1, data_10_302.2]

/-- Complete interval computation for depth 10, residue 303. -/
theorem bounds_10_303 : exactInterval 10 303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_303 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 303) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_303 : oddCount 303 10 = 7 ∧ acceleratedOrbit 10 303 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_303 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 303) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_303.1, data_10_303.2]

/-- Complete interval computation for depth 10, residue 304. -/
theorem bounds_10_304 : exactInterval 10 304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_304 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 304) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_304 : oddCount 304 10 = 4 ∧ acceleratedOrbit 10 304 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_304 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 304) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_304.1, data_10_304.2]

/-- Complete interval computation for depth 10, residue 305. -/
theorem bounds_10_305 : exactInterval 10 305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_305 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 305) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_305 : oddCount 305 10 = 5 ∧ acceleratedOrbit 10 305 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_305 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 305) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_305.1, data_10_305.2]

/-- Complete interval computation for depth 10, residue 306. -/
theorem bounds_10_306 : exactInterval 10 306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_306 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 306) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_306 : oddCount 306 10 = 5 ∧ acceleratedOrbit 10 306 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_306 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 306) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_306.1, data_10_306.2]

end Collatz.Research.StoppingAtlas.Batch0020
