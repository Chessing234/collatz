import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0499

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 481. -/
theorem bounds_13_481 : exactInterval 13 481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_481 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 481) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_481 : oddCount 481 13 = 6 ∧ acceleratedOrbit 13 481 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_481 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 481) = 3 ^ 6 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_481.1, data_13_481.2]

/-- Complete interval computation for depth 13, residue 482. -/
theorem bounds_13_482 : exactInterval 13 482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_482 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 482) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_482 : oddCount 482 13 = 4 ∧ acceleratedOrbit 13 482 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_482 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 482) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_482.1, data_13_482.2]

/-- Complete interval computation for depth 13, residue 483. -/
theorem bounds_13_483 : exactInterval 13 483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_483 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 483) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_483 : oddCount 483 13 = 4 ∧ acceleratedOrbit 13 483 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_483 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 483) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_483.1, data_13_483.2]

/-- Complete interval computation for depth 13, residue 484. -/
theorem bounds_13_484 : exactInterval 13 484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_484 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 484) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_484 : oddCount 484 13 = 8 ∧ acceleratedOrbit 13 484 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_484 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 484) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_484.1, data_13_484.2]

/-- Complete interval computation for depth 13, residue 485. -/
theorem bounds_13_485 : exactInterval 13 485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_485 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 485) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_485 : oddCount 485 13 = 8 ∧ acceleratedOrbit 13 485 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_485 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 485) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_485.1, data_13_485.2]

/-- Complete interval computation for depth 13, residue 486. -/
theorem bounds_13_486 : exactInterval 13 486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_486 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 486) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_486 : oddCount 486 13 = 8 ∧ acceleratedOrbit 13 486 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_486 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 486) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_486.1, data_13_486.2]

/-- Complete interval computation for depth 13, residue 487. -/
theorem bounds_13_487 : exactInterval 13 487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_487 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 487) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_487 : oddCount 487 13 = 9 ∧ acceleratedOrbit 13 487 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_487 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 487) = 3 ^ 9 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_487.1, data_13_487.2]

/-- Complete interval computation for depth 13, residue 488. -/
theorem bounds_13_488 : exactInterval 13 488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_488 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 488) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_488 : oddCount 488 13 = 4 ∧ acceleratedOrbit 13 488 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_488 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 488) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_488.1, data_13_488.2]

/-- Complete interval computation for depth 13, residue 489. -/
theorem bounds_13_489 : exactInterval 13 489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_489 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 489) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_489 : oddCount 489 13 = 7 ∧ acceleratedOrbit 13 489 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_489 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 489) = 3 ^ 7 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_489.1, data_13_489.2]

/-- Complete interval computation for depth 13, residue 490. -/
theorem bounds_13_490 : exactInterval 13 490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_490 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 490) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_490 : oddCount 490 13 = 4 ∧ acceleratedOrbit 13 490 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_490 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 490) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_490.1, data_13_490.2]

/-- Complete interval computation for depth 13, residue 491. -/
theorem bounds_13_491 : exactInterval 13 491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_491 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 491) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_491 : oddCount 491 13 = 10 ∧ acceleratedOrbit 13 491 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_491 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 491) = 3 ^ 10 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_491.1, data_13_491.2]

/-- Complete interval computation for depth 13, residue 492. -/
theorem bounds_13_492 : exactInterval 13 492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_492 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 492) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_492 : oddCount 492 13 = 7 ∧ acceleratedOrbit 13 492 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_492 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 492) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_492.1, data_13_492.2]

/-- Complete interval computation for depth 13, residue 493. -/
theorem bounds_13_493 : exactInterval 13 493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_493 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 493) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_493 : oddCount 493 13 = 7 ∧ acceleratedOrbit 13 493 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_493 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 493) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_493.1, data_13_493.2]

/-- Complete interval computation for depth 13, residue 494. -/
theorem bounds_13_494 : exactInterval 13 494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_494 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 494) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_494 : oddCount 494 13 = 7 ∧ acceleratedOrbit 13 494 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_494 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 494) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_494.1, data_13_494.2]

/-- Complete interval computation for depth 13, residue 495. -/
theorem bounds_13_495 : exactInterval 13 495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_495 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 495) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_495 : oddCount 495 13 = 10 ∧ acceleratedOrbit 13 495 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_495 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 495) = 3 ^ 10 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_495.1, data_13_495.2]

end Collatz.Research.StoppingAtlas.Batch0499
