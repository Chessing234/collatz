import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0099

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 481. -/
theorem bounds_11_481 : exactInterval 11 481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_481 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 481) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_481 : oddCount 481 11 = 6 ∧ acceleratedOrbit 11 481 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_481 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 481) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_481.1, data_11_481.2]

/-- Complete interval computation for depth 11, residue 482. -/
theorem bounds_11_482 : exactInterval 11 482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_482 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 482) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_482 : oddCount 482 11 = 4 ∧ acceleratedOrbit 11 482 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_482 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 482) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_482.1, data_11_482.2]

/-- Complete interval computation for depth 11, residue 483. -/
theorem bounds_11_483 : exactInterval 11 483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_483 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 483) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_483 : oddCount 483 11 = 4 ∧ acceleratedOrbit 11 483 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_483 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 483) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_483.1, data_11_483.2]

/-- Complete interval computation for depth 11, residue 484. -/
theorem bounds_11_484 : exactInterval 11 484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_484 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 484) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_484 : oddCount 484 11 = 6 ∧ acceleratedOrbit 11 484 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_484 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 484) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_484.1, data_11_484.2]

/-- Complete interval computation for depth 11, residue 485. -/
theorem bounds_11_485 : exactInterval 11 485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_485 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 485) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_485 : oddCount 485 11 = 6 ∧ acceleratedOrbit 11 485 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_485 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 485) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_485.1, data_11_485.2]

/-- Complete interval computation for depth 11, residue 486. -/
theorem bounds_11_486 : exactInterval 11 486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_486 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 486) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_486 : oddCount 486 11 = 6 ∧ acceleratedOrbit 11 486 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_486 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 486) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_486.1, data_11_486.2]

/-- Complete interval computation for depth 11, residue 487. -/
theorem bounds_11_487 : exactInterval 11 487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_487 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 487) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_487 : oddCount 487 11 = 8 ∧ acceleratedOrbit 11 487 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_487 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 487) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_487.1, data_11_487.2]

/-- Complete interval computation for depth 11, residue 488. -/
theorem bounds_11_488 : exactInterval 11 488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_488 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 488) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_488 : oddCount 488 11 = 4 ∧ acceleratedOrbit 11 488 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_488 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 488) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_488.1, data_11_488.2]

/-- Complete interval computation for depth 11, residue 489. -/
theorem bounds_11_489 : exactInterval 11 489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_489 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 489) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_489 : oddCount 489 11 = 7 ∧ acceleratedOrbit 11 489 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_489 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 489) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_489.1, data_11_489.2]

/-- Complete interval computation for depth 11, residue 490. -/
theorem bounds_11_490 : exactInterval 11 490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_490 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 490) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_490 : oddCount 490 11 = 4 ∧ acceleratedOrbit 11 490 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_490 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 490) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_490.1, data_11_490.2]

/-- Complete interval computation for depth 11, residue 491. -/
theorem bounds_11_491 : exactInterval 11 491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_491 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 491) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_491 : oddCount 491 11 = 8 ∧ acceleratedOrbit 11 491 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_491 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 491) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_491.1, data_11_491.2]

/-- Complete interval computation for depth 11, residue 492. -/
theorem bounds_11_492 : exactInterval 11 492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_492 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 492) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_492 : oddCount 492 11 = 5 ∧ acceleratedOrbit 11 492 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_492 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 492) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_492.1, data_11_492.2]

/-- Complete interval computation for depth 11, residue 493. -/
theorem bounds_11_493 : exactInterval 11 493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_493 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 493) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_493 : oddCount 493 11 = 5 ∧ acceleratedOrbit 11 493 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_493 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 493) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_493.1, data_11_493.2]

/-- Complete interval computation for depth 11, residue 494. -/
theorem bounds_11_494 : exactInterval 11 494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_494 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 494) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_494 : oddCount 494 11 = 5 ∧ acceleratedOrbit 11 494 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_494 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 494) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_494.1, data_11_494.2]

/-- Complete interval computation for depth 11, residue 495. -/
theorem bounds_11_495 : exactInterval 11 495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_495 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 495) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_495 : oddCount 495 11 = 9 ∧ acceleratedOrbit 11 495 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_495 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 495) = 3 ^ 9 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_495.1, data_11_495.2]

end Collatz.Research.StoppingAtlas.Batch0099
