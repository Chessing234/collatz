import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0471

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15400. -/
theorem bounds_15_15400 : exactInterval 15 15400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15400 : oddCount 15400 15 = 6 ∧ acceleratedOrbit 15 15400 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15400) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15400.1, data_15_15400.2]

/-- Complete interval computation for depth 15, residue 15401. -/
theorem bounds_15_15401 : exactInterval 15 15401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15401 : oddCount 15401 15 = 7 ∧ acceleratedOrbit 15 15401 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15401) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15401.1, data_15_15401.2]

/-- Complete interval computation for depth 15, residue 15402. -/
theorem bounds_15_15402 : exactInterval 15 15402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15402 : oddCount 15402 15 = 6 ∧ acceleratedOrbit 15 15402 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15402) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15402.1, data_15_15402.2]

/-- Complete interval computation for depth 15, residue 15403. -/
theorem bounds_15_15403 : exactInterval 15 15403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15403 : oddCount 15403 15 = 6 ∧ acceleratedOrbit 15 15403 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15403) = 3 ^ 6 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15403.1, data_15_15403.2]

/-- Complete interval computation for depth 15, residue 15404. -/
theorem bounds_15_15404 : exactInterval 15 15404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15404 : oddCount 15404 15 = 6 ∧ acceleratedOrbit 15 15404 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15404) = 3 ^ 6 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15404.1, data_15_15404.2]

/-- Complete interval computation for depth 15, residue 15405. -/
theorem bounds_15_15405 : exactInterval 15 15405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15405 : oddCount 15405 15 = 6 ∧ acceleratedOrbit 15 15405 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15405) = 3 ^ 6 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15405.1, data_15_15405.2]

/-- Complete interval computation for depth 15, residue 15406. -/
theorem bounds_15_15406 : exactInterval 15 15406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15406 : oddCount 15406 15 = 6 ∧ acceleratedOrbit 15 15406 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15406) = 3 ^ 6 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15406.1, data_15_15406.2]

/-- Complete interval computation for depth 15, residue 15407. -/
theorem bounds_15_15407 : exactInterval 15 15407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15407 : oddCount 15407 15 = 9 ∧ acceleratedOrbit 15 15407 = 9256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15407) = 3 ^ 9 * m + 9256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15407.1, data_15_15407.2]

/-- Complete interval computation for depth 15, residue 15408. -/
theorem bounds_15_15408 : exactInterval 15 15408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15408 : oddCount 15408 15 = 6 ∧ acceleratedOrbit 15 15408 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15408) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15408.1, data_15_15408.2]

/-- Complete interval computation for depth 15, residue 15409. -/
theorem bounds_15_15409 : exactInterval 15 15409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15409 : oddCount 15409 15 = 6 ∧ acceleratedOrbit 15 15409 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15409) = 3 ^ 6 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15409.1, data_15_15409.2]

/-- Complete interval computation for depth 15, residue 15410. -/
theorem bounds_15_15410 : exactInterval 15 15410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15410 : oddCount 15410 15 = 6 ∧ acceleratedOrbit 15 15410 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15410) = 3 ^ 6 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15410.1, data_15_15410.2]

/-- Complete interval computation for depth 15, residue 15411. -/
theorem bounds_15_15411 : exactInterval 15 15411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15411 : oddCount 15411 15 = 6 ∧ acceleratedOrbit 15 15411 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15411) = 3 ^ 6 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15411.1, data_15_15411.2]

/-- Complete interval computation for depth 15, residue 15412. -/
theorem bounds_15_15412 : exactInterval 15 15412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15412 : oddCount 15412 15 = 6 ∧ acceleratedOrbit 15 15412 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15412) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15412.1, data_15_15412.2]

/-- Complete interval computation for depth 15, residue 15413. -/
theorem bounds_15_15413 : exactInterval 15 15413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15413 : oddCount 15413 15 = 6 ∧ acceleratedOrbit 15 15413 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15413) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15413.1, data_15_15413.2]

/-- Complete interval computation for depth 15, residue 15414. -/
theorem bounds_15_15414 : exactInterval 15 15414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15414 : oddCount 15414 15 = 11 ∧ acceleratedOrbit 15 15414 = 83348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15414) = 3 ^ 11 * m + 83348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15414.1, data_15_15414.2]

/-- Complete interval computation for depth 15, residue 15415. -/
theorem bounds_15_15415 : exactInterval 15 15415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15415 : oddCount 15415 15 = 11 ∧ acceleratedOrbit 15 15415 = 83348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15415) = 3 ^ 11 * m + 83348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15415.1, data_15_15415.2]

/-- Complete interval computation for depth 15, residue 15416. -/
theorem bounds_15_15416 : exactInterval 15 15416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15416 : oddCount 15416 15 = 6 ∧ acceleratedOrbit 15 15416 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15416) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15416.1, data_15_15416.2]

/-- Complete interval computation for depth 15, residue 15417. -/
theorem bounds_15_15417 : exactInterval 15 15417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15417 : oddCount 15417 15 = 8 ∧ acceleratedOrbit 15 15417 = 3088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15417) = 3 ^ 8 * m + 3088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15417.1, data_15_15417.2]

/-- Complete interval computation for depth 15, residue 15418. -/
theorem bounds_15_15418 : exactInterval 15 15418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15418 : oddCount 15418 15 = 6 ∧ acceleratedOrbit 15 15418 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15418) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15418.1, data_15_15418.2]

/-- Complete interval computation for depth 15, residue 15419. -/
theorem bounds_15_15419 : exactInterval 15 15419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15419 : oddCount 15419 15 = 8 ∧ acceleratedOrbit 15 15419 = 3088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15419) = 3 ^ 8 * m + 3088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15419.1, data_15_15419.2]

/-- Complete interval computation for depth 15, residue 15420. -/
theorem bounds_15_15420 : exactInterval 15 15420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15420 : oddCount 15420 15 = 6 ∧ acceleratedOrbit 15 15420 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15420) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15420.1, data_15_15420.2]

/-- Complete interval computation for depth 15, residue 15421. -/
theorem bounds_15_15421 : exactInterval 15 15421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15421 : oddCount 15421 15 = 6 ∧ acceleratedOrbit 15 15421 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15421) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15421.1, data_15_15421.2]

/-- Complete interval computation for depth 15, residue 15422. -/
theorem bounds_15_15422 : exactInterval 15 15422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15422 : oddCount 15422 15 = 10 ∧ acceleratedOrbit 15 15422 = 27796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15422) = 3 ^ 10 * m + 27796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15422.1, data_15_15422.2]

/-- Complete interval computation for depth 15, residue 15423. -/
theorem bounds_15_15423 : exactInterval 15 15423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15423 : oddCount 15423 15 = 10 ∧ acceleratedOrbit 15 15423 = 27796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15423) = 3 ^ 10 * m + 27796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15423.1, data_15_15423.2]

/-- Complete interval computation for depth 15, residue 15424. -/
theorem bounds_15_15424 : exactInterval 15 15424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15424 : oddCount 15424 15 = 3 ∧ acceleratedOrbit 15 15424 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15424) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15424.1, data_15_15424.2]

/-- Complete interval computation for depth 15, residue 15425. -/
theorem bounds_15_15425 : exactInterval 15 15425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15425 : oddCount 15425 15 = 8 ∧ acceleratedOrbit 15 15425 = 3091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15425) = 3 ^ 8 * m + 3091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15425.1, data_15_15425.2]

/-- Complete interval computation for depth 15, residue 15426. -/
theorem bounds_15_15426 : exactInterval 15 15426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15426 : oddCount 15426 15 = 8 ∧ acceleratedOrbit 15 15426 = 3091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15426) = 3 ^ 8 * m + 3091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15426.1, data_15_15426.2]

/-- Complete interval computation for depth 15, residue 15427. -/
theorem bounds_15_15427 : exactInterval 15 15427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15427 : oddCount 15427 15 = 8 ∧ acceleratedOrbit 15 15427 = 3091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15427) = 3 ^ 8 * m + 3091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15427.1, data_15_15427.2]

/-- Complete interval computation for depth 15, residue 15428. -/
theorem bounds_15_15428 : exactInterval 15 15428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15428 : oddCount 15428 15 = 6 ∧ acceleratedOrbit 15 15428 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15428) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15428.1, data_15_15428.2]

/-- Complete interval computation for depth 15, residue 15429. -/
theorem bounds_15_15429 : exactInterval 15 15429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15429 : oddCount 15429 15 = 6 ∧ acceleratedOrbit 15 15429 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15429) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15429.1, data_15_15429.2]

/-- Complete interval computation for depth 15, residue 15430. -/
theorem bounds_15_15430 : exactInterval 15 15430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15430 : oddCount 15430 15 = 6 ∧ acceleratedOrbit 15 15430 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15430) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15430.1, data_15_15430.2]

/-- Complete interval computation for depth 15, residue 15431. -/
theorem bounds_15_15431 : exactInterval 15 15431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15431 : oddCount 15431 15 = 7 ∧ acceleratedOrbit 15 15431 = 1030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15431) = 3 ^ 7 * m + 1030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15431.1, data_15_15431.2]

/-- Complete interval computation for depth 15, residue 15432. -/
theorem bounds_15_15432 : exactInterval 15 15432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15432 : oddCount 15432 15 = 7 ∧ acceleratedOrbit 15 15432 = 1031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15432) = 3 ^ 7 * m + 1031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15432.1, data_15_15432.2]

end Collatz.Research.PassageAtlas.Batch0471
