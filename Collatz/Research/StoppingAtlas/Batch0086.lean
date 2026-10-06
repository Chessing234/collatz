import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0086

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 281. -/
theorem bounds_11_281 : exactInterval 11 281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_281 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 281) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_281 : oddCount 281 11 = 6 ∧ acceleratedOrbit 11 281 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_281 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 281) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_281.1, data_11_281.2]

/-- Complete interval computation for depth 11, residue 282. -/
theorem bounds_11_282 : exactInterval 11 282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_282 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 282) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_282 : oddCount 282 11 = 3 ∧ acceleratedOrbit 11 282 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_282 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 282) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_282.1, data_11_282.2]

/-- Complete interval computation for depth 11, residue 283. -/
theorem bounds_11_283 : exactInterval 11 283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_283 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 283) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_283 : oddCount 283 11 = 8 ∧ acceleratedOrbit 11 283 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_283 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 283) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_283.1, data_11_283.2]

/-- Complete interval computation for depth 11, residue 284. -/
theorem bounds_11_284 : exactInterval 11 284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_284 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 284) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_284 : oddCount 284 11 = 6 ∧ acceleratedOrbit 11 284 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_284 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 284) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_284.1, data_11_284.2]

/-- Complete interval computation for depth 11, residue 285. -/
theorem bounds_11_285 : exactInterval 11 285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_285 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 285) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_285 : oddCount 285 11 = 6 ∧ acceleratedOrbit 11 285 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_285 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 285) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_285.1, data_11_285.2]

/-- Complete interval computation for depth 11, residue 286. -/
theorem bounds_11_286 : exactInterval 11 286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_286 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 286) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_286 : oddCount 286 11 = 6 ∧ acceleratedOrbit 11 286 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_286 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 286) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_286.1, data_11_286.2]

/-- Complete interval computation for depth 11, residue 287. -/
theorem bounds_11_287 : exactInterval 11 287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_287 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 287) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_287 : oddCount 287 11 = 7 ∧ acceleratedOrbit 11 287 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_287 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 287) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_287.1, data_11_287.2]

/-- Complete interval computation for depth 11, residue 288. -/
theorem bounds_11_288 : exactInterval 11 288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_288 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 288) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_288 : oddCount 288 11 = 4 ∧ acceleratedOrbit 11 288 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_288 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 288) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_288.1, data_11_288.2]

/-- Complete interval computation for depth 11, residue 289. -/
theorem bounds_11_289 : exactInterval 11 289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_289 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 289) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_289 : oddCount 289 11 = 5 ∧ acceleratedOrbit 11 289 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_289 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 289) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_289.1, data_11_289.2]

/-- Complete interval computation for depth 11, residue 290. -/
theorem bounds_11_290 : exactInterval 11 290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_290 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 290) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_290 : oddCount 290 11 = 6 ∧ acceleratedOrbit 11 290 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_290 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 290) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_290.1, data_11_290.2]

/-- Complete interval computation for depth 11, residue 291. -/
theorem bounds_11_291 : exactInterval 11 291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_291 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 291) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_291 : oddCount 291 11 = 6 ∧ acceleratedOrbit 11 291 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_291 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 291) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_291.1, data_11_291.2]

/-- Complete interval computation for depth 11, residue 292. -/
theorem bounds_11_292 : exactInterval 11 292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_292 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 292) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_292 : oddCount 292 11 = 6 ∧ acceleratedOrbit 11 292 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_292 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 292) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_292.1, data_11_292.2]

/-- Complete interval computation for depth 11, residue 293. -/
theorem bounds_11_293 : exactInterval 11 293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_293 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 293) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_293 : oddCount 293 11 = 6 ∧ acceleratedOrbit 11 293 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_293 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 293) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_293.1, data_11_293.2]

/-- Complete interval computation for depth 11, residue 294. -/
theorem bounds_11_294 : exactInterval 11 294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_294 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 294) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_294 : oddCount 294 11 = 6 ∧ acceleratedOrbit 11 294 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_294 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 294) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_294.1, data_11_294.2]

/-- Complete interval computation for depth 11, residue 295. -/
theorem bounds_11_295 : exactInterval 11 295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_295 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 295) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_295 : oddCount 295 11 = 7 ∧ acceleratedOrbit 11 295 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_295 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 295) = 3 ^ 7 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_295.1, data_11_295.2]

end Collatz.Research.StoppingAtlas.Batch0086
