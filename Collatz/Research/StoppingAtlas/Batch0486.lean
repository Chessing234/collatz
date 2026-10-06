import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0486

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 281. -/
theorem bounds_13_281 : exactInterval 13 281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_281 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 281) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_281 : oddCount 281 13 = 7 ∧ acceleratedOrbit 13 281 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_281 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 281) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_281.1, data_13_281.2]

/-- Complete interval computation for depth 13, residue 282. -/
theorem bounds_13_282 : exactInterval 13 282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_282 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 282) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_282 : oddCount 282 13 = 3 ∧ acceleratedOrbit 13 282 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_282 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 282) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_282.1, data_13_282.2]

/-- Complete interval computation for depth 13, residue 283. -/
theorem bounds_13_283 : exactInterval 13 283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_283 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 283) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_283 : oddCount 283 13 = 10 ∧ acceleratedOrbit 13 283 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_283 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 283) = 3 ^ 10 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_283.1, data_13_283.2]

/-- Complete interval computation for depth 13, residue 284. -/
theorem bounds_13_284 : exactInterval 13 284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_284 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 284) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_284 : oddCount 284 13 = 8 ∧ acceleratedOrbit 13 284 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_284 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 284) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_284.1, data_13_284.2]

/-- Complete interval computation for depth 13, residue 285. -/
theorem bounds_13_285 : exactInterval 13 285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_285 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 285) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_285 : oddCount 285 13 = 8 ∧ acceleratedOrbit 13 285 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_285 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 285) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_285.1, data_13_285.2]

/-- Complete interval computation for depth 13, residue 286. -/
theorem bounds_13_286 : exactInterval 13 286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_286 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 286) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_286 : oddCount 286 13 = 8 ∧ acceleratedOrbit 13 286 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_286 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 286) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_286.1, data_13_286.2]

/-- Complete interval computation for depth 13, residue 287. -/
theorem bounds_13_287 : exactInterval 13 287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_287 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 287) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_287 : oddCount 287 13 = 7 ∧ acceleratedOrbit 13 287 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_287 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 287) = 3 ^ 7 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_287.1, data_13_287.2]

/-- Complete interval computation for depth 13, residue 288. -/
theorem bounds_13_288 : exactInterval 13 288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_288 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 288) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_288 : oddCount 288 13 = 5 ∧ acceleratedOrbit 13 288 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_288 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 288) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_288.1, data_13_288.2]

/-- Complete interval computation for depth 13, residue 289. -/
theorem bounds_13_289 : exactInterval 13 289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_289 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 289) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_289 : oddCount 289 13 = 7 ∧ acceleratedOrbit 13 289 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_289 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 289) = 3 ^ 7 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_289.1, data_13_289.2]

/-- Complete interval computation for depth 13, residue 290. -/
theorem bounds_13_290 : exactInterval 13 290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_290 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 290) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_290 : oddCount 290 13 = 8 ∧ acceleratedOrbit 13 290 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_290 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 290) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_290.1, data_13_290.2]

/-- Complete interval computation for depth 13, residue 291. -/
theorem bounds_13_291 : exactInterval 13 291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_291 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 291) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_291 : oddCount 291 13 = 8 ∧ acceleratedOrbit 13 291 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_291 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 291) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_291.1, data_13_291.2]

/-- Complete interval computation for depth 13, residue 292. -/
theorem bounds_13_292 : exactInterval 13 292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_292 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 292) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_292 : oddCount 292 13 = 8 ∧ acceleratedOrbit 13 292 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_292 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 292) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_292.1, data_13_292.2]

/-- Complete interval computation for depth 13, residue 293. -/
theorem bounds_13_293 : exactInterval 13 293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_293 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 293) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_293 : oddCount 293 13 = 8 ∧ acceleratedOrbit 13 293 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_293 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 293) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_293.1, data_13_293.2]

/-- Complete interval computation for depth 13, residue 294. -/
theorem bounds_13_294 : exactInterval 13 294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_294 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 294) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_294 : oddCount 294 13 = 8 ∧ acceleratedOrbit 13 294 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_294 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 294) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_294.1, data_13_294.2]

/-- Complete interval computation for depth 13, residue 295. -/
theorem bounds_13_295 : exactInterval 13 295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_295 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 295) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_295 : oddCount 295 13 = 8 ∧ acceleratedOrbit 13 295 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_295 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 295) = 3 ^ 8 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_295.1, data_13_295.2]

end Collatz.Research.StoppingAtlas.Batch0486
