import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0986

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32276. -/
theorem bounds_15_32276 : exactInterval 15 32276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32276 : oddCount 32276 15 = 8 ∧ acceleratedOrbit 15 32276 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32276) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32276.1, data_15_32276.2]

/-- Complete interval computation for depth 15, residue 32277. -/
theorem bounds_15_32277 : exactInterval 15 32277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32277 : oddCount 32277 15 = 8 ∧ acceleratedOrbit 15 32277 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32277) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32277.1, data_15_32277.2]

/-- Complete interval computation for depth 15, residue 32278. -/
theorem bounds_15_32278 : exactInterval 15 32278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32278 : oddCount 32278 15 = 7 ∧ acceleratedOrbit 15 32278 = 2155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32278) = 3 ^ 7 * m + 2155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32278.1, data_15_32278.2]

/-- Complete interval computation for depth 15, residue 32279. -/
theorem bounds_15_32279 : exactInterval 15 32279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32279 : oddCount 32279 15 = 7 ∧ acceleratedOrbit 15 32279 = 2155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32279) = 3 ^ 7 * m + 2155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32279.1, data_15_32279.2]

/-- Complete interval computation for depth 15, residue 32280. -/
theorem bounds_15_32280 : exactInterval 15 32280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32280 : oddCount 32280 15 = 8 ∧ acceleratedOrbit 15 32280 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32280) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32280.1, data_15_32280.2]

/-- Complete interval computation for depth 15, residue 32281. -/
theorem bounds_15_32281 : exactInterval 15 32281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32281 : oddCount 32281 15 = 7 ∧ acceleratedOrbit 15 32281 = 2155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32281) = 3 ^ 7 * m + 2155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32281.1, data_15_32281.2]

/-- Complete interval computation for depth 15, residue 32282. -/
theorem bounds_15_32282 : exactInterval 15 32282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32282 : oddCount 32282 15 = 8 ∧ acceleratedOrbit 15 32282 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32282) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32282.1, data_15_32282.2]

/-- Complete interval computation for depth 15, residue 32283. -/
theorem bounds_15_32283 : exactInterval 15 32283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32283 : oddCount 32283 15 = 10 ∧ acceleratedOrbit 15 32283 = 58178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32283) = 3 ^ 10 * m + 58178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32283.1, data_15_32283.2]

/-- Complete interval computation for depth 15, residue 32284. -/
theorem bounds_15_32284 : exactInterval 15 32284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32284 : oddCount 32284 15 = 6 ∧ acceleratedOrbit 15 32284 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32284) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32284.1, data_15_32284.2]

/-- Complete interval computation for depth 15, residue 32285. -/
theorem bounds_15_32285 : exactInterval 15 32285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32285 : oddCount 32285 15 = 6 ∧ acceleratedOrbit 15 32285 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32285) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32285.1, data_15_32285.2]

/-- Complete interval computation for depth 15, residue 32286. -/
theorem bounds_15_32286 : exactInterval 15 32286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32286 : oddCount 32286 15 = 6 ∧ acceleratedOrbit 15 32286 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32286) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32286.1, data_15_32286.2]

/-- Complete interval computation for depth 15, residue 32287. -/
theorem bounds_15_32287 : exactInterval 15 32287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32287 : oddCount 32287 15 = 12 ∧ acceleratedOrbit 15 32287 = 523664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32287) = 3 ^ 12 * m + 523664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32287.1, data_15_32287.2]

/-- Complete interval computation for depth 15, residue 32288. -/
theorem bounds_15_32288 : exactInterval 15 32288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32288 : oddCount 32288 15 = 5 ∧ acceleratedOrbit 15 32288 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32288) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32288.1, data_15_32288.2]

/-- Complete interval computation for depth 15, residue 32289. -/
theorem bounds_15_32289 : exactInterval 15 32289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32289 : oddCount 32289 15 = 9 ∧ acceleratedOrbit 15 32289 = 19399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32289) = 3 ^ 9 * m + 19399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32289.1, data_15_32289.2]

/-- Complete interval computation for depth 15, residue 32290. -/
theorem bounds_15_32290 : exactInterval 15 32290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32290 : oddCount 32290 15 = 8 ∧ acceleratedOrbit 15 32290 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32290) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32290.1, data_15_32290.2]

/-- Complete interval computation for depth 15, residue 32291. -/
theorem bounds_15_32291 : exactInterval 15 32291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32291 : oddCount 32291 15 = 8 ∧ acceleratedOrbit 15 32291 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32291) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32291.1, data_15_32291.2]

/-- Complete interval computation for depth 15, residue 32292. -/
theorem bounds_15_32292 : exactInterval 15 32292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32292 : oddCount 32292 15 = 9 ∧ acceleratedOrbit 15 32292 = 19403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32292) = 3 ^ 9 * m + 19403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32292.1, data_15_32292.2]

/-- Complete interval computation for depth 15, residue 32293. -/
theorem bounds_15_32293 : exactInterval 15 32293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32293 : oddCount 32293 15 = 9 ∧ acceleratedOrbit 15 32293 = 19403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32293) = 3 ^ 9 * m + 19403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32293.1, data_15_32293.2]

/-- Complete interval computation for depth 15, residue 32294. -/
theorem bounds_15_32294 : exactInterval 15 32294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32294 : oddCount 32294 15 = 9 ∧ acceleratedOrbit 15 32294 = 19403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32294) = 3 ^ 9 * m + 19403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32294.1, data_15_32294.2]

/-- Complete interval computation for depth 15, residue 32295. -/
theorem bounds_15_32295 : exactInterval 15 32295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32295 : oddCount 32295 15 = 6 ∧ acceleratedOrbit 15 32295 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32295) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32295.1, data_15_32295.2]

/-- Complete interval computation for depth 15, residue 32296. -/
theorem bounds_15_32296 : exactInterval 15 32296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32296 : oddCount 32296 15 = 5 ∧ acceleratedOrbit 15 32296 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32296) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32296.1, data_15_32296.2]

/-- Complete interval computation for depth 15, residue 32297. -/
theorem bounds_15_32297 : exactInterval 15 32297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32297 : oddCount 32297 15 = 11 ∧ acceleratedOrbit 15 32297 = 174611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32297) = 3 ^ 11 * m + 174611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32297.1, data_15_32297.2]

/-- Complete interval computation for depth 15, residue 32298. -/
theorem bounds_15_32298 : exactInterval 15 32298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32298 : oddCount 32298 15 = 5 ∧ acceleratedOrbit 15 32298 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32298) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32298.1, data_15_32298.2]

/-- Complete interval computation for depth 15, residue 32299. -/
theorem bounds_15_32299 : exactInterval 15 32299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32299 : oddCount 32299 15 = 8 ∧ acceleratedOrbit 15 32299 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32299) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32299.1, data_15_32299.2]

/-- Complete interval computation for depth 15, residue 32300. -/
theorem bounds_15_32300 : exactInterval 15 32300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32300 : oddCount 32300 15 = 8 ∧ acceleratedOrbit 15 32300 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32300) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32300.1, data_15_32300.2]

/-- Complete interval computation for depth 15, residue 32301. -/
theorem bounds_15_32301 : exactInterval 15 32301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32301 : oddCount 32301 15 = 8 ∧ acceleratedOrbit 15 32301 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32301) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32301.1, data_15_32301.2]

/-- Complete interval computation for depth 15, residue 32302. -/
theorem bounds_15_32302 : exactInterval 15 32302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32302 : oddCount 32302 15 = 8 ∧ acceleratedOrbit 15 32302 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32302) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32302.1, data_15_32302.2]

/-- Complete interval computation for depth 15, residue 32303. -/
theorem bounds_15_32303 : exactInterval 15 32303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32303 : oddCount 32303 15 = 10 ∧ acceleratedOrbit 15 32303 = 58214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32303) = 3 ^ 10 * m + 58214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32303.1, data_15_32303.2]

/-- Complete interval computation for depth 15, residue 32304. -/
theorem bounds_15_32304 : exactInterval 15 32304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32304 : oddCount 32304 15 = 5 ∧ acceleratedOrbit 15 32304 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32304) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32304.1, data_15_32304.2]

/-- Complete interval computation for depth 15, residue 32305. -/
theorem bounds_15_32305 : exactInterval 15 32305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32305 : oddCount 32305 15 = 10 ∧ acceleratedOrbit 15 32305 = 58229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32305) = 3 ^ 10 * m + 58229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32305.1, data_15_32305.2]

/-- Complete interval computation for depth 15, residue 32306. -/
theorem bounds_15_32306 : exactInterval 15 32306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32306 : oddCount 32306 15 = 10 ∧ acceleratedOrbit 15 32306 = 58229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32306) = 3 ^ 10 * m + 58229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32306.1, data_15_32306.2]

/-- Complete interval computation for depth 15, residue 32307. -/
theorem bounds_15_32307 : exactInterval 15 32307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32307 : oddCount 32307 15 = 10 ∧ acceleratedOrbit 15 32307 = 58229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32307) = 3 ^ 10 * m + 58229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32307.1, data_15_32307.2]

/-- Complete interval computation for depth 15, residue 32308. -/
theorem bounds_15_32308 : exactInterval 15 32308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32308 : oddCount 32308 15 = 5 ∧ acceleratedOrbit 15 32308 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32308) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32308.1, data_15_32308.2]

end Collatz.Research.PassageAtlas.Batch0986
