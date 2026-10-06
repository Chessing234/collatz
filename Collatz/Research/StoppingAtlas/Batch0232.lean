import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0232

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 476. -/
theorem bounds_12_476 : exactInterval 12 476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_476 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 476) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_476 : oddCount 476 12 = 5 ∧ acceleratedOrbit 12 476 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_476 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 476) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_476.1, data_12_476.2]

/-- Complete interval computation for depth 12, residue 477. -/
theorem bounds_12_477 : exactInterval 12 477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_477 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 477) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_477 : oddCount 477 12 = 5 ∧ acceleratedOrbit 12 477 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_477 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 477) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_477.1, data_12_477.2]

/-- Complete interval computation for depth 12, residue 478. -/
theorem bounds_12_478 : exactInterval 12 478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_478 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 478) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_478 : oddCount 478 12 = 9 ∧ acceleratedOrbit 12 478 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_478 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 478) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_478.1, data_12_478.2]

/-- Complete interval computation for depth 12, residue 479. -/
theorem bounds_12_479 : exactInterval 12 479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_479 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 479) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_479 : oddCount 479 12 = 9 ∧ acceleratedOrbit 12 479 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_479 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 479) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_479.1, data_12_479.2]

/-- Complete interval computation for depth 12, residue 480. -/
theorem bounds_12_480 : exactInterval 12 480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_480 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 480) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_480 : oddCount 480 12 = 4 ∧ acceleratedOrbit 12 480 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_480 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 480) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_480.1, data_12_480.2]

/-- Complete interval computation for depth 12, residue 481. -/
theorem bounds_12_481 : exactInterval 12 481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_481 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 481) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_481 : oddCount 481 12 = 6 ∧ acceleratedOrbit 12 481 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_481 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 481) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_481.1, data_12_481.2]

/-- Complete interval computation for depth 12, residue 482. -/
theorem bounds_12_482 : exactInterval 12 482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_482 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 482) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_482 : oddCount 482 12 = 4 ∧ acceleratedOrbit 12 482 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_482 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 482) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_482.1, data_12_482.2]

/-- Complete interval computation for depth 12, residue 483. -/
theorem bounds_12_483 : exactInterval 12 483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_483 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 483) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_483 : oddCount 483 12 = 4 ∧ acceleratedOrbit 12 483 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_483 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 483) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_483.1, data_12_483.2]

/-- Complete interval computation for depth 12, residue 484. -/
theorem bounds_12_484 : exactInterval 12 484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_484 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 484) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_484 : oddCount 484 12 = 7 ∧ acceleratedOrbit 12 484 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_484 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 484) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_484.1, data_12_484.2]

/-- Complete interval computation for depth 12, residue 485. -/
theorem bounds_12_485 : exactInterval 12 485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_485 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 485) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_485 : oddCount 485 12 = 7 ∧ acceleratedOrbit 12 485 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_485 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 485) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_485.1, data_12_485.2]

/-- Complete interval computation for depth 12, residue 486. -/
theorem bounds_12_486 : exactInterval 12 486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_486 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 486) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_486 : oddCount 486 12 = 7 ∧ acceleratedOrbit 12 486 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_486 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 486) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_486.1, data_12_486.2]

/-- Complete interval computation for depth 12, residue 487. -/
theorem bounds_12_487 : exactInterval 12 487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_487 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 487) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_487 : oddCount 487 12 = 9 ∧ acceleratedOrbit 12 487 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_487 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 487) = 3 ^ 9 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_487.1, data_12_487.2]

/-- Complete interval computation for depth 12, residue 488. -/
theorem bounds_12_488 : exactInterval 12 488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_488 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 488) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_488 : oddCount 488 12 = 4 ∧ acceleratedOrbit 12 488 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_488 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 488) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_488.1, data_12_488.2]

/-- Complete interval computation for depth 12, residue 489. -/
theorem bounds_12_489 : exactInterval 12 489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_489 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 489) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_489 : oddCount 489 12 = 7 ∧ acceleratedOrbit 12 489 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_489 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 489) = 3 ^ 7 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_489.1, data_12_489.2]

/-- Complete interval computation for depth 12, residue 490. -/
theorem bounds_12_490 : exactInterval 12 490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_490 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 490) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_490 : oddCount 490 12 = 4 ∧ acceleratedOrbit 12 490 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_490 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 490) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_490.1, data_12_490.2]

end Collatz.Research.StoppingAtlas.Batch0232
