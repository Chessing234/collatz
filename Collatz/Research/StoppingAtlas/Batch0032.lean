import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0032

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 476. -/
theorem bounds_10_476 : exactInterval 10 476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_476 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 476) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_476 : oddCount 476 10 = 4 ∧ acceleratedOrbit 10 476 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_476 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 476) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_476.1, data_10_476.2]

/-- Complete interval computation for depth 10, residue 477. -/
theorem bounds_10_477 : exactInterval 10 477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_477 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 477) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_477 : oddCount 477 10 = 4 ∧ acceleratedOrbit 10 477 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_477 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 477) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_477.1, data_10_477.2]

/-- Complete interval computation for depth 10, residue 478. -/
theorem bounds_10_478 : exactInterval 10 478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_478 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 478) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_478 : oddCount 478 10 = 8 ∧ acceleratedOrbit 10 478 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_478 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 478) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_478.1, data_10_478.2]

/-- Complete interval computation for depth 10, residue 479. -/
theorem bounds_10_479 : exactInterval 10 479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_479 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 479) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_479 : oddCount 479 10 = 8 ∧ acceleratedOrbit 10 479 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_479 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 479) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_479.1, data_10_479.2]

/-- Complete interval computation for depth 10, residue 480. -/
theorem bounds_10_480 : exactInterval 10 480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_480 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 480) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_480 : oddCount 480 10 = 4 ∧ acceleratedOrbit 10 480 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_480 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 480) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_480.1, data_10_480.2]

/-- Complete interval computation for depth 10, residue 481. -/
theorem bounds_10_481 : exactInterval 10 481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_481 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 481) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_481 : oddCount 481 10 = 6 ∧ acceleratedOrbit 10 481 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_481 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 481) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_481.1, data_10_481.2]

/-- Complete interval computation for depth 10, residue 482. -/
theorem bounds_10_482 : exactInterval 10 482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_482 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 482) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_482 : oddCount 482 10 = 3 ∧ acceleratedOrbit 10 482 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_482 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 482) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_482.1, data_10_482.2]

/-- Complete interval computation for depth 10, residue 483. -/
theorem bounds_10_483 : exactInterval 10 483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_483 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 483) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_483 : oddCount 483 10 = 3 ∧ acceleratedOrbit 10 483 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_483 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 483) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_483.1, data_10_483.2]

/-- Complete interval computation for depth 10, residue 484. -/
theorem bounds_10_484 : exactInterval 10 484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_484 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 484) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_484 : oddCount 484 10 = 6 ∧ acceleratedOrbit 10 484 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_484 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 484) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_484.1, data_10_484.2]

/-- Complete interval computation for depth 10, residue 485. -/
theorem bounds_10_485 : exactInterval 10 485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_485 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 485) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_485 : oddCount 485 10 = 6 ∧ acceleratedOrbit 10 485 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_485 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 485) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_485.1, data_10_485.2]

/-- Complete interval computation for depth 10, residue 486. -/
theorem bounds_10_486 : exactInterval 10 486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_486 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 486) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_486 : oddCount 486 10 = 6 ∧ acceleratedOrbit 10 486 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_486 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 486) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_486.1, data_10_486.2]

/-- Complete interval computation for depth 10, residue 487. -/
theorem bounds_10_487 : exactInterval 10 487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_487 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 487) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_487 : oddCount 487 10 = 7 ∧ acceleratedOrbit 10 487 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_487 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 487) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_487.1, data_10_487.2]

/-- Complete interval computation for depth 10, residue 488. -/
theorem bounds_10_488 : exactInterval 10 488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_488 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 488) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_488 : oddCount 488 10 = 4 ∧ acceleratedOrbit 10 488 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_488 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 488) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_488.1, data_10_488.2]

/-- Complete interval computation for depth 10, residue 489. -/
theorem bounds_10_489 : exactInterval 10 489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_489 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 489) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_489 : oddCount 489 10 = 7 ∧ acceleratedOrbit 10 489 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_489 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 489) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_489.1, data_10_489.2]

/-- Complete interval computation for depth 10, residue 490. -/
theorem bounds_10_490 : exactInterval 10 490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_490 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 490) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_490 : oddCount 490 10 = 4 ∧ acceleratedOrbit 10 490 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_490 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 490) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_490.1, data_10_490.2]

end Collatz.Research.StoppingAtlas.Batch0032
