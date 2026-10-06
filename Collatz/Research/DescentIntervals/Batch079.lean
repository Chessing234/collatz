import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch079

/-- Complete interval computation for depth 9, residue 287. -/
theorem bounds_9_287 : exactInterval 9 287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_287 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 287) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_287 : oddCount 287 9 = 6 ∧ acceleratedOrbit 9 287 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_287 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 287) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_287.1, data_9_287.2]

/-- Complete interval computation for depth 9, residue 288. -/
theorem bounds_9_288 : exactInterval 9 288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_288 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 288) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_288 : oddCount 288 9 = 3 ∧ acceleratedOrbit 9 288 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_288 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 288) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_288.1, data_9_288.2]

/-- Complete interval computation for depth 9, residue 289. -/
theorem bounds_9_289 : exactInterval 9 289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_289 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 289) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_289 : oddCount 289 9 = 4 ∧ acceleratedOrbit 9 289 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_289 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 289) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_289.1, data_9_289.2]

/-- Complete interval computation for depth 9, residue 290. -/
theorem bounds_9_290 : exactInterval 9 290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_290 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 290) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_290 : oddCount 290 9 = 4 ∧ acceleratedOrbit 9 290 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_290 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 290) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_290.1, data_9_290.2]

/-- Complete interval computation for depth 9, residue 291. -/
theorem bounds_9_291 : exactInterval 9 291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_291 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 291) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_291 : oddCount 291 9 = 4 ∧ acceleratedOrbit 9 291 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_291 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 291) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_291.1, data_9_291.2]

/-- Complete interval computation for depth 9, residue 292. -/
theorem bounds_9_292 : exactInterval 9 292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_292 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 292) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_292 : oddCount 292 9 = 4 ∧ acceleratedOrbit 9 292 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_292 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 292) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_292.1, data_9_292.2]

/-- Complete interval computation for depth 9, residue 293. -/
theorem bounds_9_293 : exactInterval 9 293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_293 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 293) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_293 : oddCount 293 9 = 4 ∧ acceleratedOrbit 9 293 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_293 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 293) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_293.1, data_9_293.2]

/-- Complete interval computation for depth 9, residue 294. -/
theorem bounds_9_294 : exactInterval 9 294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_294 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 294) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_294 : oddCount 294 9 = 4 ∧ acceleratedOrbit 9 294 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_294 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 294) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_294.1, data_9_294.2]

/-- Complete interval computation for depth 9, residue 295. -/
theorem bounds_9_295 : exactInterval 9 295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_295 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 295) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_295 : oddCount 295 9 = 6 ∧ acceleratedOrbit 9 295 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_295 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 295) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_295.1, data_9_295.2]

/-- Complete interval computation for depth 9, residue 296. -/
theorem bounds_9_296 : exactInterval 9 296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_296 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 296) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_296 : oddCount 296 9 = 3 ∧ acceleratedOrbit 9 296 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_296 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 296) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_296.1, data_9_296.2]

end Collatz.Research.DescentIntervals.Batch079
