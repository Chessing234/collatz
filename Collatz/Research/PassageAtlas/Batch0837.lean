import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0837

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27394. -/
theorem bounds_15_27394 : exactInterval 15 27394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27394 : oddCount 27394 15 = 7 ∧ acceleratedOrbit 15 27394 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27394) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27394.1, data_15_27394.2]

/-- Complete interval computation for depth 15, residue 27395. -/
theorem bounds_15_27395 : exactInterval 15 27395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27395 : oddCount 27395 15 = 7 ∧ acceleratedOrbit 15 27395 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27395) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27395.1, data_15_27395.2]

/-- Complete interval computation for depth 15, residue 27396. -/
theorem bounds_15_27396 : exactInterval 15 27396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27396 : oddCount 27396 15 = 6 ∧ acceleratedOrbit 15 27396 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27396) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27396.1, data_15_27396.2]

/-- Complete interval computation for depth 15, residue 27397. -/
theorem bounds_15_27397 : exactInterval 15 27397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27397 : oddCount 27397 15 = 6 ∧ acceleratedOrbit 15 27397 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27397) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27397.1, data_15_27397.2]

/-- Complete interval computation for depth 15, residue 27398. -/
theorem bounds_15_27398 : exactInterval 15 27398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27398 : oddCount 27398 15 = 6 ∧ acceleratedOrbit 15 27398 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27398) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27398.1, data_15_27398.2]

/-- Complete interval computation for depth 15, residue 27399. -/
theorem bounds_15_27399 : exactInterval 15 27399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27399 : oddCount 27399 15 = 9 ∧ acceleratedOrbit 15 27399 = 16460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27399) = 3 ^ 9 * m + 16460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27399.1, data_15_27399.2]

/-- Complete interval computation for depth 15, residue 27400. -/
theorem bounds_15_27400 : exactInterval 15 27400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27400 : oddCount 27400 15 = 6 ∧ acceleratedOrbit 15 27400 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27400) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27400.1, data_15_27400.2]

/-- Complete interval computation for depth 15, residue 27401. -/
theorem bounds_15_27401 : exactInterval 15 27401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27401 : oddCount 27401 15 = 11 ∧ acceleratedOrbit 15 27401 = 148148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27401) = 3 ^ 11 * m + 148148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27401.1, data_15_27401.2]

/-- Complete interval computation for depth 15, residue 27402. -/
theorem bounds_15_27402 : exactInterval 15 27402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27402 : oddCount 27402 15 = 6 ∧ acceleratedOrbit 15 27402 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27402) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27402.1, data_15_27402.2]

/-- Complete interval computation for depth 15, residue 27403. -/
theorem bounds_15_27403 : exactInterval 15 27403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27403 : oddCount 27403 15 = 9 ∧ acceleratedOrbit 15 27403 = 16463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27403) = 3 ^ 9 * m + 16463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27403.1, data_15_27403.2]

/-- Complete interval computation for depth 15, residue 27404. -/
theorem bounds_15_27404 : exactInterval 15 27404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27404 : oddCount 27404 15 = 6 ∧ acceleratedOrbit 15 27404 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27404) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27404.1, data_15_27404.2]

/-- Complete interval computation for depth 15, residue 27405. -/
theorem bounds_15_27405 : exactInterval 15 27405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27405 : oddCount 27405 15 = 6 ∧ acceleratedOrbit 15 27405 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27405) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27405.1, data_15_27405.2]

/-- Complete interval computation for depth 15, residue 27406. -/
theorem bounds_15_27406 : exactInterval 15 27406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27406 : oddCount 27406 15 = 6 ∧ acceleratedOrbit 15 27406 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27406) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27406.1, data_15_27406.2]

/-- Complete interval computation for depth 15, residue 27407. -/
theorem bounds_15_27407 : exactInterval 15 27407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27407 : oddCount 27407 15 = 6 ∧ acceleratedOrbit 15 27407 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27407) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27407.1, data_15_27407.2]

/-- Complete interval computation for depth 15, residue 27408. -/
theorem bounds_15_27408 : exactInterval 15 27408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27408 : oddCount 27408 15 = 4 ∧ acceleratedOrbit 15 27408 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27408) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27408.1, data_15_27408.2]

/-- Complete interval computation for depth 15, residue 27409. -/
theorem bounds_15_27409 : exactInterval 15 27409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27409 : oddCount 27409 15 = 6 ∧ acceleratedOrbit 15 27409 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27409) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27409.1, data_15_27409.2]

/-- Complete interval computation for depth 15, residue 27410. -/
theorem bounds_15_27410 : exactInterval 15 27410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27410 : oddCount 27410 15 = 9 ∧ acceleratedOrbit 15 27410 = 16469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27410) = 3 ^ 9 * m + 16469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27410.1, data_15_27410.2]

/-- Complete interval computation for depth 15, residue 27411. -/
theorem bounds_15_27411 : exactInterval 15 27411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27411 : oddCount 27411 15 = 9 ∧ acceleratedOrbit 15 27411 = 16469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27411) = 3 ^ 9 * m + 16469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27411.1, data_15_27411.2]

/-- Complete interval computation for depth 15, residue 27412. -/
theorem bounds_15_27412 : exactInterval 15 27412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27412 : oddCount 27412 15 = 4 ∧ acceleratedOrbit 15 27412 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27412) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27412.1, data_15_27412.2]

/-- Complete interval computation for depth 15, residue 27413. -/
theorem bounds_15_27413 : exactInterval 15 27413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27413 : oddCount 27413 15 = 4 ∧ acceleratedOrbit 15 27413 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27413) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27413.1, data_15_27413.2]

/-- Complete interval computation for depth 15, residue 27414. -/
theorem bounds_15_27414 : exactInterval 15 27414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27414 : oddCount 27414 15 = 6 ∧ acceleratedOrbit 15 27414 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27414) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27414.1, data_15_27414.2]

/-- Complete interval computation for depth 15, residue 27415. -/
theorem bounds_15_27415 : exactInterval 15 27415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27415 : oddCount 27415 15 = 6 ∧ acceleratedOrbit 15 27415 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27415) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27415.1, data_15_27415.2]

/-- Complete interval computation for depth 15, residue 27416. -/
theorem bounds_15_27416 : exactInterval 15 27416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27416 : oddCount 27416 15 = 4 ∧ acceleratedOrbit 15 27416 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27416) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27416.1, data_15_27416.2]

/-- Complete interval computation for depth 15, residue 27417. -/
theorem bounds_15_27417 : exactInterval 15 27417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27417 : oddCount 27417 15 = 9 ∧ acceleratedOrbit 15 27417 = 16471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27417) = 3 ^ 9 * m + 16471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27417.1, data_15_27417.2]

/-- Complete interval computation for depth 15, residue 27418. -/
theorem bounds_15_27418 : exactInterval 15 27418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27418 : oddCount 27418 15 = 4 ∧ acceleratedOrbit 15 27418 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27418) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27418.1, data_15_27418.2]

/-- Complete interval computation for depth 15, residue 27419. -/
theorem bounds_15_27419 : exactInterval 15 27419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27419 : oddCount 27419 15 = 11 ∧ acceleratedOrbit 15 27419 = 148238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27419) = 3 ^ 11 * m + 148238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27419.1, data_15_27419.2]

/-- Complete interval computation for depth 15, residue 27420. -/
theorem bounds_15_27420 : exactInterval 15 27420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27420 : oddCount 27420 15 = 7 ∧ acceleratedOrbit 15 27420 = 1831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27420) = 3 ^ 7 * m + 1831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27420.1, data_15_27420.2]

/-- Complete interval computation for depth 15, residue 27421. -/
theorem bounds_15_27421 : exactInterval 15 27421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27421 : oddCount 27421 15 = 7 ∧ acceleratedOrbit 15 27421 = 1831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27421) = 3 ^ 7 * m + 1831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27421.1, data_15_27421.2]

/-- Complete interval computation for depth 15, residue 27422. -/
theorem bounds_15_27422 : exactInterval 15 27422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27422 : oddCount 27422 15 = 7 ∧ acceleratedOrbit 15 27422 = 1831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27422) = 3 ^ 7 * m + 1831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27422.1, data_15_27422.2]

/-- Complete interval computation for depth 15, residue 27423. -/
theorem bounds_15_27423 : exactInterval 15 27423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27423 : oddCount 27423 15 = 10 ∧ acceleratedOrbit 15 27423 = 49420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27423) = 3 ^ 10 * m + 49420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27423.1, data_15_27423.2]

/-- Complete interval computation for depth 15, residue 27424. -/
theorem bounds_15_27424 : exactInterval 15 27424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27424 : oddCount 27424 15 = 4 ∧ acceleratedOrbit 15 27424 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27424) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27424.1, data_15_27424.2]

/-- Complete interval computation for depth 15, residue 27425. -/
theorem bounds_15_27425 : exactInterval 15 27425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27425 : oddCount 27425 15 = 7 ∧ acceleratedOrbit 15 27425 = 1831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27425) = 3 ^ 7 * m + 1831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27425.1, data_15_27425.2]

end Collatz.Research.PassageAtlas.Batch0837
