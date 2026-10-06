import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0427

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3471. -/
theorem bounds_12_3471 : exactInterval 12 3471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3471 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3471) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3471 : oddCount 3471 12 = 5 ∧ acceleratedOrbit 12 3471 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3471 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3471) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3471.1, data_12_3471.2]

/-- Complete interval computation for depth 12, residue 3472. -/
theorem bounds_12_3472 : exactInterval 12 3472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3472 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3472) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3472 : oddCount 3472 12 = 3 ∧ acceleratedOrbit 12 3472 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3472 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3472) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3472.1, data_12_3472.2]

/-- Complete interval computation for depth 12, residue 3473. -/
theorem bounds_12_3473 : exactInterval 12 3473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3473 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3473) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3473 : oddCount 3473 12 = 6 ∧ acceleratedOrbit 12 3473 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3473 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3473) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3473.1, data_12_3473.2]

/-- Complete interval computation for depth 12, residue 3474. -/
theorem bounds_12_3474 : exactInterval 12 3474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3474 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3474) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3474 : oddCount 3474 12 = 6 ∧ acceleratedOrbit 12 3474 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3474 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3474) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3474.1, data_12_3474.2]

/-- Complete interval computation for depth 12, residue 3475. -/
theorem bounds_12_3475 : exactInterval 12 3475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3475 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3475) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3475 : oddCount 3475 12 = 6 ∧ acceleratedOrbit 12 3475 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3475 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3475) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3475.1, data_12_3475.2]

/-- Complete interval computation for depth 12, residue 3476. -/
theorem bounds_12_3476 : exactInterval 12 3476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3476 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3476) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3476 : oddCount 3476 12 = 3 ∧ acceleratedOrbit 12 3476 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3476 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3476) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3476.1, data_12_3476.2]

/-- Complete interval computation for depth 12, residue 3477. -/
theorem bounds_12_3477 : exactInterval 12 3477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3477 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3477) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3477 : oddCount 3477 12 = 3 ∧ acceleratedOrbit 12 3477 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3477 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3477) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3477.1, data_12_3477.2]

/-- Complete interval computation for depth 12, residue 3478. -/
theorem bounds_12_3478 : exactInterval 12 3478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3478 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3478) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3478 : oddCount 3478 12 = 7 ∧ acceleratedOrbit 12 3478 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3478 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3478) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3478.1, data_12_3478.2]

/-- Complete interval computation for depth 12, residue 3479. -/
theorem bounds_12_3479 : exactInterval 12 3479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3479 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3479) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3479 : oddCount 3479 12 = 7 ∧ acceleratedOrbit 12 3479 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3479 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3479) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3479.1, data_12_3479.2]

/-- Complete interval computation for depth 12, residue 3480. -/
theorem bounds_12_3480 : exactInterval 12 3480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3480 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3480) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3480 : oddCount 3480 12 = 3 ∧ acceleratedOrbit 12 3480 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3480 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3480) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3480.1, data_12_3480.2]

/-- Complete interval computation for depth 12, residue 3481. -/
theorem bounds_12_3481 : exactInterval 12 3481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3481 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3481) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3481 : oddCount 3481 12 = 7 ∧ acceleratedOrbit 12 3481 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3481 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3481) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3481.1, data_12_3481.2]

/-- Complete interval computation for depth 12, residue 3482. -/
theorem bounds_12_3482 : exactInterval 12 3482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3482 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3482) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3482 : oddCount 3482 12 = 3 ∧ acceleratedOrbit 12 3482 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3482 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3482) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3482.1, data_12_3482.2]

/-- Complete interval computation for depth 12, residue 3483. -/
theorem bounds_12_3483 : exactInterval 12 3483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3483 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3483) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3483 : oddCount 3483 12 = 8 ∧ acceleratedOrbit 12 3483 = 5582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3483 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3483) = 3 ^ 8 * m + 5582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3483.1, data_12_3483.2]

/-- Complete interval computation for depth 12, residue 3484. -/
theorem bounds_12_3484 : exactInterval 12 3484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3484 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3484) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3484 : oddCount 3484 12 = 9 ∧ acceleratedOrbit 12 3484 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3484 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3484) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3484.1, data_12_3484.2]

/-- Complete interval computation for depth 12, residue 3485. -/
theorem bounds_12_3485 : exactInterval 12 3485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3485 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3485) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3485 : oddCount 3485 12 = 9 ∧ acceleratedOrbit 12 3485 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3485 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3485) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3485.1, data_12_3485.2]

end Collatz.Research.StoppingAtlas.Batch0427
