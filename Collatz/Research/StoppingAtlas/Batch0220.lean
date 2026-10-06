import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0220

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 291. -/
theorem bounds_12_291 : exactInterval 12 291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_291 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 291) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_291 : oddCount 291 12 = 7 ∧ acceleratedOrbit 12 291 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_291 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 291) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_291.1, data_12_291.2]

/-- Complete interval computation for depth 12, residue 292. -/
theorem bounds_12_292 : exactInterval 12 292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_292 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 292) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_292 : oddCount 292 12 = 7 ∧ acceleratedOrbit 12 292 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_292 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 292) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_292.1, data_12_292.2]

/-- Complete interval computation for depth 12, residue 293. -/
theorem bounds_12_293 : exactInterval 12 293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_293 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 293) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_293 : oddCount 293 12 = 7 ∧ acceleratedOrbit 12 293 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_293 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 293) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_293.1, data_12_293.2]

/-- Complete interval computation for depth 12, residue 294. -/
theorem bounds_12_294 : exactInterval 12 294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_294 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 294) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_294 : oddCount 294 12 = 7 ∧ acceleratedOrbit 12 294 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_294 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 294) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_294.1, data_12_294.2]

/-- Complete interval computation for depth 12, residue 295. -/
theorem bounds_12_295 : exactInterval 12 295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_295 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 295) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_295 : oddCount 295 12 = 8 ∧ acceleratedOrbit 12 295 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_295 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 295) = 3 ^ 8 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_295.1, data_12_295.2]

/-- Complete interval computation for depth 12, residue 296. -/
theorem bounds_12_296 : exactInterval 12 296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_296 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 296) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_296 : oddCount 296 12 = 5 ∧ acceleratedOrbit 12 296 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_296 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 296) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_296.1, data_12_296.2]

/-- Complete interval computation for depth 12, residue 297. -/
theorem bounds_12_297 : exactInterval 12 297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_297 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 297) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_297 : oddCount 297 12 = 8 ∧ acceleratedOrbit 12 297 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_297 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 297) = 3 ^ 8 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_297.1, data_12_297.2]

/-- Complete interval computation for depth 12, residue 298. -/
theorem bounds_12_298 : exactInterval 12 298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_298 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 298) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_298 : oddCount 298 12 = 5 ∧ acceleratedOrbit 12 298 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_298 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 298) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_298.1, data_12_298.2]

/-- Complete interval computation for depth 12, residue 299. -/
theorem bounds_12_299 : exactInterval 12 299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_299 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 299) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_299 : oddCount 299 12 = 8 ∧ acceleratedOrbit 12 299 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_299 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 299) = 3 ^ 8 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_299.1, data_12_299.2]

/-- Complete interval computation for depth 12, residue 300. -/
theorem bounds_12_300 : exactInterval 12 300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_300 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 300) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_300 : oddCount 300 12 = 3 ∧ acceleratedOrbit 12 300 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_300 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 300) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_300.1, data_12_300.2]

/-- Complete interval computation for depth 12, residue 301. -/
theorem bounds_12_301 : exactInterval 12 301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_301 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 301) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_301 : oddCount 301 12 = 3 ∧ acceleratedOrbit 12 301 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_301 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 301) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_301.1, data_12_301.2]

/-- Complete interval computation for depth 12, residue 302. -/
theorem bounds_12_302 : exactInterval 12 302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_302 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 302) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_302 : oddCount 302 12 = 3 ∧ acceleratedOrbit 12 302 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_302 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 302) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_302.1, data_12_302.2]

/-- Complete interval computation for depth 12, residue 303. -/
theorem bounds_12_303 : exactInterval 12 303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_303 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 303) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_303 : oddCount 303 12 = 8 ∧ acceleratedOrbit 12 303 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_303 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 303) = 3 ^ 8 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_303.1, data_12_303.2]

/-- Complete interval computation for depth 12, residue 304. -/
theorem bounds_12_304 : exactInterval 12 304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_304 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 304) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_304 : oddCount 304 12 = 5 ∧ acceleratedOrbit 12 304 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_304 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 304) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_304.1, data_12_304.2]

/-- Complete interval computation for depth 12, residue 305. -/
theorem bounds_12_305 : exactInterval 12 305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_305 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 305) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_305 : oddCount 305 12 = 6 ∧ acceleratedOrbit 12 305 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_305 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 305) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_305.1, data_12_305.2]

/-- Complete interval computation for depth 12, residue 306. -/
theorem bounds_12_306 : exactInterval 12 306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_306 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 306) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_306 : oddCount 306 12 = 6 ∧ acceleratedOrbit 12 306 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_306 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 306) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_306.1, data_12_306.2]

end Collatz.Research.StoppingAtlas.Batch0220
