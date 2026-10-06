import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0107

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3473. -/
theorem bounds_15_3473 : exactInterval 15 3473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3473 : oddCount 3473 15 = 7 ∧ acceleratedOrbit 15 3473 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3473) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3473.1, data_15_3473.2]

/-- Complete interval computation for depth 15, residue 3474. -/
theorem bounds_15_3474 : exactInterval 15 3474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3474 : oddCount 3474 15 = 7 ∧ acceleratedOrbit 15 3474 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3474) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3474.1, data_15_3474.2]

/-- Complete interval computation for depth 15, residue 3475. -/
theorem bounds_15_3475 : exactInterval 15 3475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3475 : oddCount 3475 15 = 7 ∧ acceleratedOrbit 15 3475 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3475) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3475.1, data_15_3475.2]

/-- Complete interval computation for depth 15, residue 3476. -/
theorem bounds_15_3476 : exactInterval 15 3476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3476 : oddCount 3476 15 = 6 ∧ acceleratedOrbit 15 3476 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3476) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3476.1, data_15_3476.2]

/-- Complete interval computation for depth 15, residue 3477. -/
theorem bounds_15_3477 : exactInterval 15 3477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3477 : oddCount 3477 15 = 6 ∧ acceleratedOrbit 15 3477 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3477) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3477.1, data_15_3477.2]

/-- Complete interval computation for depth 15, residue 3478. -/
theorem bounds_15_3478 : exactInterval 15 3478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3478 : oddCount 3478 15 = 9 ∧ acceleratedOrbit 15 3478 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3478) = 3 ^ 9 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3478.1, data_15_3478.2]

/-- Complete interval computation for depth 15, residue 3479. -/
theorem bounds_15_3479 : exactInterval 15 3479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3479 : oddCount 3479 15 = 9 ∧ acceleratedOrbit 15 3479 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3479) = 3 ^ 9 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3479.1, data_15_3479.2]

/-- Complete interval computation for depth 15, residue 3480. -/
theorem bounds_15_3480 : exactInterval 15 3480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3480 : oddCount 3480 15 = 6 ∧ acceleratedOrbit 15 3480 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3480) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3480.1, data_15_3480.2]

/-- Complete interval computation for depth 15, residue 3481. -/
theorem bounds_15_3481 : exactInterval 15 3481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3481 : oddCount 3481 15 = 9 ∧ acceleratedOrbit 15 3481 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3481) = 3 ^ 9 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3481.1, data_15_3481.2]

/-- Complete interval computation for depth 15, residue 3482. -/
theorem bounds_15_3482 : exactInterval 15 3482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3482 : oddCount 3482 15 = 6 ∧ acceleratedOrbit 15 3482 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3482) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3482.1, data_15_3482.2]

/-- Complete interval computation for depth 15, residue 3483. -/
theorem bounds_15_3483 : exactInterval 15 3483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3483 : oddCount 3483 15 = 10 ∧ acceleratedOrbit 15 3483 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3483) = 3 ^ 10 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3483.1, data_15_3483.2]

/-- Complete interval computation for depth 15, residue 3484. -/
theorem bounds_15_3484 : exactInterval 15 3484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3484 : oddCount 3484 15 = 11 ∧ acceleratedOrbit 15 3484 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3484) = 3 ^ 11 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3484.1, data_15_3484.2]

/-- Complete interval computation for depth 15, residue 3485. -/
theorem bounds_15_3485 : exactInterval 15 3485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3485 : oddCount 3485 15 = 11 ∧ acceleratedOrbit 15 3485 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3485) = 3 ^ 11 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3485.1, data_15_3485.2]

/-- Complete interval computation for depth 15, residue 3486. -/
theorem bounds_15_3486 : exactInterval 15 3486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3486 : oddCount 3486 15 = 11 ∧ acceleratedOrbit 15 3486 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3486) = 3 ^ 11 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3486.1, data_15_3486.2]

/-- Complete interval computation for depth 15, residue 3487. -/
theorem bounds_15_3487 : exactInterval 15 3487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3487 : oddCount 3487 15 = 10 ∧ acceleratedOrbit 15 3487 = 6286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3487) = 3 ^ 10 * m + 6286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3487.1, data_15_3487.2]

/-- Complete interval computation for depth 15, residue 3488. -/
theorem bounds_15_3488 : exactInterval 15 3488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3488 : oddCount 3488 15 = 7 ∧ acceleratedOrbit 15 3488 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3488) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3488.1, data_15_3488.2]

/-- Complete interval computation for depth 15, residue 3489. -/
theorem bounds_15_3489 : exactInterval 15 3489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3489 : oddCount 3489 15 = 9 ∧ acceleratedOrbit 15 3489 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3489) = 3 ^ 9 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3489.1, data_15_3489.2]

/-- Complete interval computation for depth 15, residue 3490. -/
theorem bounds_15_3490 : exactInterval 15 3490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3490 : oddCount 3490 15 = 9 ∧ acceleratedOrbit 15 3490 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3490) = 3 ^ 9 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3490.1, data_15_3490.2]

/-- Complete interval computation for depth 15, residue 3491. -/
theorem bounds_15_3491 : exactInterval 15 3491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3491 : oddCount 3491 15 = 9 ∧ acceleratedOrbit 15 3491 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3491) = 3 ^ 9 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3491.1, data_15_3491.2]

/-- Complete interval computation for depth 15, residue 3492. -/
theorem bounds_15_3492 : exactInterval 15 3492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3492 : oddCount 3492 15 = 9 ∧ acceleratedOrbit 15 3492 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3492) = 3 ^ 9 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3492.1, data_15_3492.2]

/-- Complete interval computation for depth 15, residue 3493. -/
theorem bounds_15_3493 : exactInterval 15 3493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3493 : oddCount 3493 15 = 9 ∧ acceleratedOrbit 15 3493 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3493) = 3 ^ 9 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3493.1, data_15_3493.2]

/-- Complete interval computation for depth 15, residue 3494. -/
theorem bounds_15_3494 : exactInterval 15 3494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3494 : oddCount 3494 15 = 9 ∧ acceleratedOrbit 15 3494 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3494) = 3 ^ 9 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3494.1, data_15_3494.2]

/-- Complete interval computation for depth 15, residue 3495. -/
theorem bounds_15_3495 : exactInterval 15 3495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3495 : oddCount 3495 15 = 9 ∧ acceleratedOrbit 15 3495 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3495) = 3 ^ 9 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3495.1, data_15_3495.2]

/-- Complete interval computation for depth 15, residue 3496. -/
theorem bounds_15_3496 : exactInterval 15 3496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3496 : oddCount 3496 15 = 7 ∧ acceleratedOrbit 15 3496 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3496) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3496.1, data_15_3496.2]

/-- Complete interval computation for depth 15, residue 3497. -/
theorem bounds_15_3497 : exactInterval 15 3497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3497 : oddCount 3497 15 = 8 ∧ acceleratedOrbit 15 3497 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3497) = 3 ^ 8 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3497.1, data_15_3497.2]

/-- Complete interval computation for depth 15, residue 3498. -/
theorem bounds_15_3498 : exactInterval 15 3498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3498 : oddCount 3498 15 = 7 ∧ acceleratedOrbit 15 3498 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3498) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3498.1, data_15_3498.2]

/-- Complete interval computation for depth 15, residue 3499. -/
theorem bounds_15_3499 : exactInterval 15 3499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3499 : oddCount 3499 15 = 10 ∧ acceleratedOrbit 15 3499 = 6311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3499) = 3 ^ 10 * m + 6311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3499.1, data_15_3499.2]

/-- Complete interval computation for depth 15, residue 3500. -/
theorem bounds_15_3500 : exactInterval 15 3500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3500 : oddCount 3500 15 = 5 ∧ acceleratedOrbit 15 3500 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3500) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3500.1, data_15_3500.2]

/-- Complete interval computation for depth 15, residue 3501. -/
theorem bounds_15_3501 : exactInterval 15 3501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3501 : oddCount 3501 15 = 5 ∧ acceleratedOrbit 15 3501 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3501) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3501.1, data_15_3501.2]

/-- Complete interval computation for depth 15, residue 3502. -/
theorem bounds_15_3502 : exactInterval 15 3502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3502 : oddCount 3502 15 = 5 ∧ acceleratedOrbit 15 3502 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3502) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3502.1, data_15_3502.2]

/-- Complete interval computation for depth 15, residue 3503. -/
theorem bounds_15_3503 : exactInterval 15 3503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3503 : oddCount 3503 15 = 11 ∧ acceleratedOrbit 15 3503 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3503) = 3 ^ 11 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3503.1, data_15_3503.2]

/-- Complete interval computation for depth 15, residue 3504. -/
theorem bounds_15_3504 : exactInterval 15 3504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3504 : oddCount 3504 15 = 7 ∧ acceleratedOrbit 15 3504 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3504) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3504.1, data_15_3504.2]

/-- Complete interval computation for depth 15, residue 3505. -/
theorem bounds_15_3505 : exactInterval 15 3505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3505 : oddCount 3505 15 = 7 ∧ acceleratedOrbit 15 3505 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3505) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3505.1, data_15_3505.2]

end Collatz.Research.PassageAtlas.Batch0107
