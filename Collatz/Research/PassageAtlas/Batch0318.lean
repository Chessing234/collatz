import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0318

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10387. -/
theorem bounds_15_10387 : exactInterval 15 10387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10387 : oddCount 10387 15 = 8 ∧ acceleratedOrbit 15 10387 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10387) = 3 ^ 8 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10387.1, data_15_10387.2]

/-- Complete interval computation for depth 15, residue 10388. -/
theorem bounds_15_10388 : exactInterval 15 10388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10388 : oddCount 10388 15 = 7 ∧ acceleratedOrbit 15 10388 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10388) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10388.1, data_15_10388.2]

/-- Complete interval computation for depth 15, residue 10389. -/
theorem bounds_15_10389 : exactInterval 15 10389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10389 : oddCount 10389 15 = 7 ∧ acceleratedOrbit 15 10389 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10389) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10389.1, data_15_10389.2]

/-- Complete interval computation for depth 15, residue 10390. -/
theorem bounds_15_10390 : exactInterval 15 10390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10390 : oddCount 10390 15 = 6 ∧ acceleratedOrbit 15 10390 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10390) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10390.1, data_15_10390.2]

/-- Complete interval computation for depth 15, residue 10391. -/
theorem bounds_15_10391 : exactInterval 15 10391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10391 : oddCount 10391 15 = 6 ∧ acceleratedOrbit 15 10391 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10391) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10391.1, data_15_10391.2]

/-- Complete interval computation for depth 15, residue 10392. -/
theorem bounds_15_10392 : exactInterval 15 10392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10392 : oddCount 10392 15 = 7 ∧ acceleratedOrbit 15 10392 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10392) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10392.1, data_15_10392.2]

/-- Complete interval computation for depth 15, residue 10393. -/
theorem bounds_15_10393 : exactInterval 15 10393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10393 : oddCount 10393 15 = 7 ∧ acceleratedOrbit 15 10393 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10393) = 3 ^ 7 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10393.1, data_15_10393.2]

/-- Complete interval computation for depth 15, residue 10394. -/
theorem bounds_15_10394 : exactInterval 15 10394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10394 : oddCount 10394 15 = 7 ∧ acceleratedOrbit 15 10394 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10394) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10394.1, data_15_10394.2]

/-- Complete interval computation for depth 15, residue 10395. -/
theorem bounds_15_10395 : exactInterval 15 10395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10395 : oddCount 10395 15 = 10 ∧ acceleratedOrbit 15 10395 = 18737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10395) = 3 ^ 10 * m + 18737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10395.1, data_15_10395.2]

/-- Complete interval computation for depth 15, residue 10396. -/
theorem bounds_15_10396 : exactInterval 15 10396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10396 : oddCount 10396 15 = 7 ∧ acceleratedOrbit 15 10396 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10396) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10396.1, data_15_10396.2]

/-- Complete interval computation for depth 15, residue 10397. -/
theorem bounds_15_10397 : exactInterval 15 10397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10397 : oddCount 10397 15 = 7 ∧ acceleratedOrbit 15 10397 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10397) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10397.1, data_15_10397.2]

/-- Complete interval computation for depth 15, residue 10398. -/
theorem bounds_15_10398 : exactInterval 15 10398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10398 : oddCount 10398 15 = 7 ∧ acceleratedOrbit 15 10398 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10398) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10398.1, data_15_10398.2]

/-- Complete interval computation for depth 15, residue 10399. -/
theorem bounds_15_10399 : exactInterval 15 10399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10399 : oddCount 10399 15 = 11 ∧ acceleratedOrbit 15 10399 = 56224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10399) = 3 ^ 11 * m + 56224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10399.1, data_15_10399.2]

/-- Complete interval computation for depth 15, residue 10400. -/
theorem bounds_15_10400 : exactInterval 15 10400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10400 : oddCount 10400 15 = 5 ∧ acceleratedOrbit 15 10400 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10400) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10400.1, data_15_10400.2]

/-- Complete interval computation for depth 15, residue 10401. -/
theorem bounds_15_10401 : exactInterval 15 10401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10401 : oddCount 10401 15 = 9 ∧ acceleratedOrbit 15 10401 = 6250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10401) = 3 ^ 9 * m + 6250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10401.1, data_15_10401.2]

/-- Complete interval computation for depth 15, residue 10402. -/
theorem bounds_15_10402 : exactInterval 15 10402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10402 : oddCount 10402 15 = 7 ∧ acceleratedOrbit 15 10402 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10402) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10402.1, data_15_10402.2]

/-- Complete interval computation for depth 15, residue 10403. -/
theorem bounds_15_10403 : exactInterval 15 10403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10403 : oddCount 10403 15 = 7 ∧ acceleratedOrbit 15 10403 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10403) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10403.1, data_15_10403.2]

/-- Complete interval computation for depth 15, residue 10404. -/
theorem bounds_15_10404 : exactInterval 15 10404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10404 : oddCount 10404 15 = 9 ∧ acceleratedOrbit 15 10404 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10404) = 3 ^ 9 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10404.1, data_15_10404.2]

/-- Complete interval computation for depth 15, residue 10405. -/
theorem bounds_15_10405 : exactInterval 15 10405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10405 : oddCount 10405 15 = 9 ∧ acceleratedOrbit 15 10405 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10405) = 3 ^ 9 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10405.1, data_15_10405.2]

/-- Complete interval computation for depth 15, residue 10406. -/
theorem bounds_15_10406 : exactInterval 15 10406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10406 : oddCount 10406 15 = 9 ∧ acceleratedOrbit 15 10406 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10406) = 3 ^ 9 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10406.1, data_15_10406.2]

/-- Complete interval computation for depth 15, residue 10407. -/
theorem bounds_15_10407 : exactInterval 15 10407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10407 : oddCount 10407 15 = 11 ∧ acceleratedOrbit 15 10407 = 56270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10407) = 3 ^ 11 * m + 56270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10407.1, data_15_10407.2]

/-- Complete interval computation for depth 15, residue 10408. -/
theorem bounds_15_10408 : exactInterval 15 10408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10408 : oddCount 10408 15 = 5 ∧ acceleratedOrbit 15 10408 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10408) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10408.1, data_15_10408.2]

/-- Complete interval computation for depth 15, residue 10409. -/
theorem bounds_15_10409 : exactInterval 15 10409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10409 : oddCount 10409 15 = 12 ∧ acceleratedOrbit 15 10409 = 168844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10409) = 3 ^ 12 * m + 168844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10409.1, data_15_10409.2]

/-- Complete interval computation for depth 15, residue 10410. -/
theorem bounds_15_10410 : exactInterval 15 10410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10410 : oddCount 10410 15 = 5 ∧ acceleratedOrbit 15 10410 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10410) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10410.1, data_15_10410.2]

/-- Complete interval computation for depth 15, residue 10411. -/
theorem bounds_15_10411 : exactInterval 15 10411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10411 : oddCount 10411 15 = 9 ∧ acceleratedOrbit 15 10411 = 6257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10411) = 3 ^ 9 * m + 6257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10411.1, data_15_10411.2]

/-- Complete interval computation for depth 15, residue 10412. -/
theorem bounds_15_10412 : exactInterval 15 10412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10412 : oddCount 10412 15 = 6 ∧ acceleratedOrbit 15 10412 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10412) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10412.1, data_15_10412.2]

/-- Complete interval computation for depth 15, residue 10413. -/
theorem bounds_15_10413 : exactInterval 15 10413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10413 : oddCount 10413 15 = 6 ∧ acceleratedOrbit 15 10413 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10413) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10413.1, data_15_10413.2]

/-- Complete interval computation for depth 15, residue 10414. -/
theorem bounds_15_10414 : exactInterval 15 10414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10414 : oddCount 10414 15 = 6 ∧ acceleratedOrbit 15 10414 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10414) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10414.1, data_15_10414.2]

/-- Complete interval computation for depth 15, residue 10415. -/
theorem bounds_15_10415 : exactInterval 15 10415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10415 : oddCount 10415 15 = 11 ∧ acceleratedOrbit 15 10415 = 56315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10415) = 3 ^ 11 * m + 56315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10415.1, data_15_10415.2]

/-- Complete interval computation for depth 15, residue 10416. -/
theorem bounds_15_10416 : exactInterval 15 10416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10416 : oddCount 10416 15 = 6 ∧ acceleratedOrbit 15 10416 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10416) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10416.1, data_15_10416.2]

/-- Complete interval computation for depth 15, residue 10417. -/
theorem bounds_15_10417 : exactInterval 15 10417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10417 : oddCount 10417 15 = 6 ∧ acceleratedOrbit 15 10417 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10417) = 3 ^ 6 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10417.1, data_15_10417.2]

/-- Complete interval computation for depth 15, residue 10418. -/
theorem bounds_15_10418 : exactInterval 15 10418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10418 : oddCount 10418 15 = 6 ∧ acceleratedOrbit 15 10418 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10418) = 3 ^ 6 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10418.1, data_15_10418.2]

/-- Complete interval computation for depth 15, residue 10419. -/
theorem bounds_15_10419 : exactInterval 15 10419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10419 : oddCount 10419 15 = 6 ∧ acceleratedOrbit 15 10419 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10419) = 3 ^ 6 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10419.1, data_15_10419.2]

end Collatz.Research.PassageAtlas.Batch0318
