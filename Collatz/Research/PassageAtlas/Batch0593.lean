import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0593

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19398. -/
theorem bounds_15_19398 : exactInterval 15 19398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19398 : oddCount 19398 15 = 3 ∧ acceleratedOrbit 15 19398 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19398) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19398.1, data_15_19398.2]

/-- Complete interval computation for depth 15, residue 19399. -/
theorem bounds_15_19399 : exactInterval 15 19399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19399 : oddCount 19399 15 = 11 ∧ acceleratedOrbit 15 19399 = 104885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19399) = 3 ^ 11 * m + 104885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19399.1, data_15_19399.2]

/-- Complete interval computation for depth 15, residue 19400. -/
theorem bounds_15_19400 : exactInterval 15 19400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19400 : oddCount 19400 15 = 10 ∧ acceleratedOrbit 15 19400 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19400) = 3 ^ 10 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19400.1, data_15_19400.2]

/-- Complete interval computation for depth 15, residue 19401. -/
theorem bounds_15_19401 : exactInterval 15 19401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19401 : oddCount 19401 15 = 9 ∧ acceleratedOrbit 15 19401 = 11657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19401) = 3 ^ 9 * m + 11657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19401.1, data_15_19401.2]

/-- Complete interval computation for depth 15, residue 19402. -/
theorem bounds_15_19402 : exactInterval 15 19402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19402 : oddCount 19402 15 = 10 ∧ acceleratedOrbit 15 19402 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19402) = 3 ^ 10 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19402.1, data_15_19402.2]

/-- Complete interval computation for depth 15, residue 19403. -/
theorem bounds_15_19403 : exactInterval 15 19403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19403 : oddCount 19403 15 = 9 ∧ acceleratedOrbit 15 19403 = 11663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19403) = 3 ^ 9 * m + 11663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19403.1, data_15_19403.2]

/-- Complete interval computation for depth 15, residue 19404. -/
theorem bounds_15_19404 : exactInterval 15 19404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19404 : oddCount 19404 15 = 10 ∧ acceleratedOrbit 15 19404 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19404) = 3 ^ 10 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19404.1, data_15_19404.2]

/-- Complete interval computation for depth 15, residue 19405. -/
theorem bounds_15_19405 : exactInterval 15 19405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19405 : oddCount 19405 15 = 10 ∧ acceleratedOrbit 15 19405 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19405) = 3 ^ 10 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19405.1, data_15_19405.2]

/-- Complete interval computation for depth 15, residue 19406. -/
theorem bounds_15_19406 : exactInterval 15 19406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19406 : oddCount 19406 15 = 9 ∧ acceleratedOrbit 15 19406 = 11659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19406) = 3 ^ 9 * m + 11659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19406.1, data_15_19406.2]

/-- Complete interval computation for depth 15, residue 19407. -/
theorem bounds_15_19407 : exactInterval 15 19407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19407 : oddCount 19407 15 = 9 ∧ acceleratedOrbit 15 19407 = 11659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19407) = 3 ^ 9 * m + 11659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19407.1, data_15_19407.2]

/-- Complete interval computation for depth 15, residue 19408. -/
theorem bounds_15_19408 : exactInterval 15 19408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19408 : oddCount 19408 15 = 6 ∧ acceleratedOrbit 15 19408 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19408) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19408.1, data_15_19408.2]

/-- Complete interval computation for depth 15, residue 19409. -/
theorem bounds_15_19409 : exactInterval 15 19409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19409 : oddCount 19409 15 = 10 ∧ acceleratedOrbit 15 19409 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19409) = 3 ^ 10 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19409.1, data_15_19409.2]

/-- Complete interval computation for depth 15, residue 19410. -/
theorem bounds_15_19410 : exactInterval 15 19410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19410 : oddCount 19410 15 = 10 ∧ acceleratedOrbit 15 19410 = 34985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19410) = 3 ^ 10 * m + 34985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19410.1, data_15_19410.2]

/-- Complete interval computation for depth 15, residue 19411. -/
theorem bounds_15_19411 : exactInterval 15 19411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19411 : oddCount 19411 15 = 10 ∧ acceleratedOrbit 15 19411 = 34985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19411) = 3 ^ 10 * m + 34985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19411.1, data_15_19411.2]

/-- Complete interval computation for depth 15, residue 19412. -/
theorem bounds_15_19412 : exactInterval 15 19412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19412 : oddCount 19412 15 = 6 ∧ acceleratedOrbit 15 19412 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19412) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19412.1, data_15_19412.2]

/-- Complete interval computation for depth 15, residue 19413. -/
theorem bounds_15_19413 : exactInterval 15 19413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19413 : oddCount 19413 15 = 6 ∧ acceleratedOrbit 15 19413 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19413) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19413.1, data_15_19413.2]

/-- Complete interval computation for depth 15, residue 19414. -/
theorem bounds_15_19414 : exactInterval 15 19414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19414 : oddCount 19414 15 = 12 ∧ acceleratedOrbit 15 19414 = 314927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19414) = 3 ^ 12 * m + 314927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19414.1, data_15_19414.2]

/-- Complete interval computation for depth 15, residue 19415. -/
theorem bounds_15_19415 : exactInterval 15 19415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19415 : oddCount 19415 15 = 12 ∧ acceleratedOrbit 15 19415 = 314927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19415) = 3 ^ 12 * m + 314927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19415.1, data_15_19415.2]

/-- Complete interval computation for depth 15, residue 19416. -/
theorem bounds_15_19416 : exactInterval 15 19416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19416 : oddCount 19416 15 = 7 ∧ acceleratedOrbit 15 19416 = 1297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19416) = 3 ^ 7 * m + 1297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19416.1, data_15_19416.2]

/-- Complete interval computation for depth 15, residue 19417. -/
theorem bounds_15_19417 : exactInterval 15 19417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19417 : oddCount 19417 15 = 3 ∧ acceleratedOrbit 15 19417 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19417) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19417.1, data_15_19417.2]

/-- Complete interval computation for depth 15, residue 19418. -/
theorem bounds_15_19418 : exactInterval 15 19418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19418 : oddCount 19418 15 = 7 ∧ acceleratedOrbit 15 19418 = 1297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19418) = 3 ^ 7 * m + 1297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19418.1, data_15_19418.2]

/-- Complete interval computation for depth 15, residue 19419. -/
theorem bounds_15_19419 : exactInterval 15 19419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19419 : oddCount 19419 15 = 8 ∧ acceleratedOrbit 15 19419 = 3889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19419) = 3 ^ 8 * m + 3889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19419.1, data_15_19419.2]

/-- Complete interval computation for depth 15, residue 19420. -/
theorem bounds_15_19420 : exactInterval 15 19420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19420 : oddCount 19420 15 = 7 ∧ acceleratedOrbit 15 19420 = 1297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19420) = 3 ^ 7 * m + 1297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19420.1, data_15_19420.2]

/-- Complete interval computation for depth 15, residue 19421. -/
theorem bounds_15_19421 : exactInterval 15 19421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19421 : oddCount 19421 15 = 7 ∧ acceleratedOrbit 15 19421 = 1297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19421) = 3 ^ 7 * m + 1297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19421.1, data_15_19421.2]

/-- Complete interval computation for depth 15, residue 19422. -/
theorem bounds_15_19422 : exactInterval 15 19422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19422 : oddCount 19422 15 = 9 ∧ acceleratedOrbit 15 19422 = 11668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19422) = 3 ^ 9 * m + 11668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19422.1, data_15_19422.2]

/-- Complete interval computation for depth 15, residue 19423. -/
theorem bounds_15_19423 : exactInterval 15 19423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19423 : oddCount 19423 15 = 9 ∧ acceleratedOrbit 15 19423 = 11668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19423) = 3 ^ 9 * m + 11668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19423.1, data_15_19423.2]

/-- Complete interval computation for depth 15, residue 19424. -/
theorem bounds_15_19424 : exactInterval 15 19424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19424 : oddCount 19424 15 = 6 ∧ acceleratedOrbit 15 19424 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19424) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19424.1, data_15_19424.2]

/-- Complete interval computation for depth 15, residue 19425. -/
theorem bounds_15_19425 : exactInterval 15 19425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19425 : oddCount 19425 15 = 8 ∧ acceleratedOrbit 15 19425 = 3890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19425) = 3 ^ 8 * m + 3890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19425.1, data_15_19425.2]

/-- Complete interval computation for depth 15, residue 19426. -/
theorem bounds_15_19426 : exactInterval 15 19426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19426 : oddCount 19426 15 = 6 ∧ acceleratedOrbit 15 19426 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19426) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19426.1, data_15_19426.2]

/-- Complete interval computation for depth 15, residue 19427. -/
theorem bounds_15_19427 : exactInterval 15 19427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19427 : oddCount 19427 15 = 6 ∧ acceleratedOrbit 15 19427 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19427) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19427.1, data_15_19427.2]

/-- Complete interval computation for depth 15, residue 19428. -/
theorem bounds_15_19428 : exactInterval 15 19428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19428 : oddCount 19428 15 = 7 ∧ acceleratedOrbit 15 19428 = 1298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19428) = 3 ^ 7 * m + 1298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19428.1, data_15_19428.2]

/-- Complete interval computation for depth 15, residue 19429. -/
theorem bounds_15_19429 : exactInterval 15 19429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19429 : oddCount 19429 15 = 7 ∧ acceleratedOrbit 15 19429 = 1298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19429) = 3 ^ 7 * m + 1298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19429.1, data_15_19429.2]

/-- Complete interval computation for depth 15, residue 19430. -/
theorem bounds_15_19430 : exactInterval 15 19430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19430 : oddCount 19430 15 = 7 ∧ acceleratedOrbit 15 19430 = 1298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19430) = 3 ^ 7 * m + 1298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19430.1, data_15_19430.2]

end Collatz.Research.PassageAtlas.Batch0593
