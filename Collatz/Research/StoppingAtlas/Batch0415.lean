import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0415

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3287. -/
theorem bounds_12_3287 : exactInterval 12 3287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3287 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3287) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3287 : oddCount 3287 12 = 7 ∧ acceleratedOrbit 12 3287 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3287 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3287) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3287.1, data_12_3287.2]

/-- Complete interval computation for depth 12, residue 3288. -/
theorem bounds_12_3288 : exactInterval 12 3288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3288 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3288) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3288 : oddCount 3288 12 = 6 ∧ acceleratedOrbit 12 3288 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3288 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3288) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3288.1, data_12_3288.2]

/-- Complete interval computation for depth 12, residue 3289. -/
theorem bounds_12_3289 : exactInterval 12 3289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3289 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3289) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3289 : oddCount 3289 12 = 6 ∧ acceleratedOrbit 12 3289 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3289 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3289) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3289.1, data_12_3289.2]

/-- Complete interval computation for depth 12, residue 3290. -/
theorem bounds_12_3290 : exactInterval 12 3290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3290 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3290) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3290 : oddCount 3290 12 = 6 ∧ acceleratedOrbit 12 3290 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3290 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3290) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3290.1, data_12_3290.2]

/-- Complete interval computation for depth 12, residue 3291. -/
theorem bounds_12_3291 : exactInterval 12 3291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3291 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3291) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3291 : oddCount 3291 12 = 6 ∧ acceleratedOrbit 12 3291 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3291 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3291) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3291.1, data_12_3291.2]

/-- Complete interval computation for depth 12, residue 3292. -/
theorem bounds_12_3292 : exactInterval 12 3292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3292 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3292) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3292 : oddCount 3292 12 = 6 ∧ acceleratedOrbit 12 3292 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3292 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3292) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3292.1, data_12_3292.2]

/-- Complete interval computation for depth 12, residue 3293. -/
theorem bounds_12_3293 : exactInterval 12 3293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3293 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3293) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3293 : oddCount 3293 12 = 6 ∧ acceleratedOrbit 12 3293 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3293 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3293) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3293.1, data_12_3293.2]

/-- Complete interval computation for depth 12, residue 3294. -/
theorem bounds_12_3294 : exactInterval 12 3294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3294 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3294) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3294 : oddCount 3294 12 = 7 ∧ acceleratedOrbit 12 3294 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3294 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3294) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3294.1, data_12_3294.2]

/-- Complete interval computation for depth 12, residue 3295. -/
theorem bounds_12_3295 : exactInterval 12 3295 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3295 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3295) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3295 : oddCount 3295 12 = 7 ∧ acceleratedOrbit 12 3295 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3295 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3295) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3295.1, data_12_3295.2]

/-- Complete interval computation for depth 12, residue 3296. -/
theorem bounds_12_3296 : exactInterval 12 3296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3296 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3296) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3296 : oddCount 3296 12 = 6 ∧ acceleratedOrbit 12 3296 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3296 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3296) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3296.1, data_12_3296.2]

/-- Complete interval computation for depth 12, residue 3297. -/
theorem bounds_12_3297 : exactInterval 12 3297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3297 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3297) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3297 : oddCount 3297 12 = 8 ∧ acceleratedOrbit 12 3297 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3297 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3297) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3297.1, data_12_3297.2]

/-- Complete interval computation for depth 12, residue 3298. -/
theorem bounds_12_3298 : exactInterval 12 3298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3298 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3298) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3298 : oddCount 3298 12 = 3 ∧ acceleratedOrbit 12 3298 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3298 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3298) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3298.1, data_12_3298.2]

/-- Complete interval computation for depth 12, residue 3299. -/
theorem bounds_12_3299 : exactInterval 12 3299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3299 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3299) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3299 : oddCount 3299 12 = 3 ∧ acceleratedOrbit 12 3299 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3299 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3299) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3299.1, data_12_3299.2]

/-- Complete interval computation for depth 12, residue 3300. -/
theorem bounds_12_3300 : exactInterval 12 3300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3300 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3300) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3300 : oddCount 3300 12 = 6 ∧ acceleratedOrbit 12 3300 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3300 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3300) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3300.1, data_12_3300.2]

/-- Complete interval computation for depth 12, residue 3301. -/
theorem bounds_12_3301 : exactInterval 12 3301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3301 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3301) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3301 : oddCount 3301 12 = 6 ∧ acceleratedOrbit 12 3301 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3301 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3301) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3301.1, data_12_3301.2]

end Collatz.Research.StoppingAtlas.Batch0415
