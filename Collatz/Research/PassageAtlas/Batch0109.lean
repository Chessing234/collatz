import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0109

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3538. -/
theorem bounds_15_3538 : exactInterval 15 3538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3538 : oddCount 3538 15 = 9 ∧ acceleratedOrbit 15 3538 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3538) = 3 ^ 9 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3538.1, data_15_3538.2]

/-- Complete interval computation for depth 15, residue 3539. -/
theorem bounds_15_3539 : exactInterval 15 3539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3539 : oddCount 3539 15 = 9 ∧ acceleratedOrbit 15 3539 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3539) = 3 ^ 9 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3539.1, data_15_3539.2]

/-- Complete interval computation for depth 15, residue 3540. -/
theorem bounds_15_3540 : exactInterval 15 3540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3540 : oddCount 3540 15 = 7 ∧ acceleratedOrbit 15 3540 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3540) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3540.1, data_15_3540.2]

/-- Complete interval computation for depth 15, residue 3541. -/
theorem bounds_15_3541 : exactInterval 15 3541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3541 : oddCount 3541 15 = 7 ∧ acceleratedOrbit 15 3541 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3541) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3541.1, data_15_3541.2]

/-- Complete interval computation for depth 15, residue 3542. -/
theorem bounds_15_3542 : exactInterval 15 3542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3542 : oddCount 3542 15 = 9 ∧ acceleratedOrbit 15 3542 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3542) = 3 ^ 9 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3542.1, data_15_3542.2]

/-- Complete interval computation for depth 15, residue 3543. -/
theorem bounds_15_3543 : exactInterval 15 3543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3543 : oddCount 3543 15 = 9 ∧ acceleratedOrbit 15 3543 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3543) = 3 ^ 9 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3543.1, data_15_3543.2]

/-- Complete interval computation for depth 15, residue 3544. -/
theorem bounds_15_3544 : exactInterval 15 3544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3544 : oddCount 3544 15 = 7 ∧ acceleratedOrbit 15 3544 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3544) = 3 ^ 7 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3544.1, data_15_3544.2]

/-- Complete interval computation for depth 15, residue 3545. -/
theorem bounds_15_3545 : exactInterval 15 3545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3545 : oddCount 3545 15 = 7 ∧ acceleratedOrbit 15 3545 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3545) = 3 ^ 7 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3545.1, data_15_3545.2]

/-- Complete interval computation for depth 15, residue 3546. -/
theorem bounds_15_3546 : exactInterval 15 3546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3546 : oddCount 3546 15 = 7 ∧ acceleratedOrbit 15 3546 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3546) = 3 ^ 7 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3546.1, data_15_3546.2]

/-- Complete interval computation for depth 15, residue 3547. -/
theorem bounds_15_3547 : exactInterval 15 3547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3547 : oddCount 3547 15 = 6 ∧ acceleratedOrbit 15 3547 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3547) = 3 ^ 6 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3547.1, data_15_3547.2]

/-- Complete interval computation for depth 15, residue 3548. -/
theorem bounds_15_3548 : exactInterval 15 3548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3548 : oddCount 3548 15 = 7 ∧ acceleratedOrbit 15 3548 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3548) = 3 ^ 7 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3548.1, data_15_3548.2]

/-- Complete interval computation for depth 15, residue 3549. -/
theorem bounds_15_3549 : exactInterval 15 3549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3549 : oddCount 3549 15 = 7 ∧ acceleratedOrbit 15 3549 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3549) = 3 ^ 7 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3549.1, data_15_3549.2]

/-- Complete interval computation for depth 15, residue 3550. -/
theorem bounds_15_3550 : exactInterval 15 3550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3550 : oddCount 3550 15 = 9 ∧ acceleratedOrbit 15 3550 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3550) = 3 ^ 9 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3550.1, data_15_3550.2]

/-- Complete interval computation for depth 15, residue 3551. -/
theorem bounds_15_3551 : exactInterval 15 3551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3551 : oddCount 3551 15 = 9 ∧ acceleratedOrbit 15 3551 = 2134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3551) = 3 ^ 9 * m + 2134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3551.1, data_15_3551.2]

/-- Complete interval computation for depth 15, residue 3552. -/
theorem bounds_15_3552 : exactInterval 15 3552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3552 : oddCount 3552 15 = 8 ∧ acceleratedOrbit 15 3552 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3552) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3552.1, data_15_3552.2]

/-- Complete interval computation for depth 15, residue 3553. -/
theorem bounds_15_3553 : exactInterval 15 3553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3553 : oddCount 3553 15 = 8 ∧ acceleratedOrbit 15 3553 = 712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3553) = 3 ^ 8 * m + 712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3553.1, data_15_3553.2]

/-- Complete interval computation for depth 15, residue 3554. -/
theorem bounds_15_3554 : exactInterval 15 3554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3554 : oddCount 3554 15 = 7 ∧ acceleratedOrbit 15 3554 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3554) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3554.1, data_15_3554.2]

/-- Complete interval computation for depth 15, residue 3555. -/
theorem bounds_15_3555 : exactInterval 15 3555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3555 : oddCount 3555 15 = 7 ∧ acceleratedOrbit 15 3555 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3555) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3555.1, data_15_3555.2]

/-- Complete interval computation for depth 15, residue 3556. -/
theorem bounds_15_3556 : exactInterval 15 3556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3556 : oddCount 3556 15 = 10 ∧ acceleratedOrbit 15 3556 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3556) = 3 ^ 10 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3556.1, data_15_3556.2]

/-- Complete interval computation for depth 15, residue 3557. -/
theorem bounds_15_3557 : exactInterval 15 3557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3557 : oddCount 3557 15 = 10 ∧ acceleratedOrbit 15 3557 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3557) = 3 ^ 10 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3557.1, data_15_3557.2]

/-- Complete interval computation for depth 15, residue 3558. -/
theorem bounds_15_3558 : exactInterval 15 3558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3558 : oddCount 3558 15 = 10 ∧ acceleratedOrbit 15 3558 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3558) = 3 ^ 10 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3558.1, data_15_3558.2]

/-- Complete interval computation for depth 15, residue 3559. -/
theorem bounds_15_3559 : exactInterval 15 3559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3559 : oddCount 3559 15 = 8 ∧ acceleratedOrbit 15 3559 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3559) = 3 ^ 8 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3559.1, data_15_3559.2]

/-- Complete interval computation for depth 15, residue 3560. -/
theorem bounds_15_3560 : exactInterval 15 3560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3560 : oddCount 3560 15 = 8 ∧ acceleratedOrbit 15 3560 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3560) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3560.1, data_15_3560.2]

/-- Complete interval computation for depth 15, residue 3561. -/
theorem bounds_15_3561 : exactInterval 15 3561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3561 : oddCount 3561 15 = 10 ∧ acceleratedOrbit 15 3561 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3561) = 3 ^ 10 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3561.1, data_15_3561.2]

/-- Complete interval computation for depth 15, residue 3562. -/
theorem bounds_15_3562 : exactInterval 15 3562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3562 : oddCount 3562 15 = 8 ∧ acceleratedOrbit 15 3562 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3562) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3562.1, data_15_3562.2]

/-- Complete interval computation for depth 15, residue 3563. -/
theorem bounds_15_3563 : exactInterval 15 3563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3563 : oddCount 3563 15 = 11 ∧ acceleratedOrbit 15 3563 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3563) = 3 ^ 11 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3563.1, data_15_3563.2]

/-- Complete interval computation for depth 15, residue 3564. -/
theorem bounds_15_3564 : exactInterval 15 3564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3564 : oddCount 3564 15 = 9 ∧ acceleratedOrbit 15 3564 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3564) = 3 ^ 9 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3564.1, data_15_3564.2]

/-- Complete interval computation for depth 15, residue 3565. -/
theorem bounds_15_3565 : exactInterval 15 3565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3565 : oddCount 3565 15 = 9 ∧ acceleratedOrbit 15 3565 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3565) = 3 ^ 9 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3565.1, data_15_3565.2]

/-- Complete interval computation for depth 15, residue 3566. -/
theorem bounds_15_3566 : exactInterval 15 3566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3566 : oddCount 3566 15 = 9 ∧ acceleratedOrbit 15 3566 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3566) = 3 ^ 9 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3566.1, data_15_3566.2]

/-- Complete interval computation for depth 15, residue 3567. -/
theorem bounds_15_3567 : exactInterval 15 3567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3567 : oddCount 3567 15 = 11 ∧ acceleratedOrbit 15 3567 = 19291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3567) = 3 ^ 11 * m + 19291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3567.1, data_15_3567.2]

/-- Complete interval computation for depth 15, residue 3568. -/
theorem bounds_15_3568 : exactInterval 15 3568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3568 : oddCount 3568 15 = 8 ∧ acceleratedOrbit 15 3568 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3568) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3568.1, data_15_3568.2]

/-- Complete interval computation for depth 15, residue 3569. -/
theorem bounds_15_3569 : exactInterval 15 3569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3569 : oddCount 3569 15 = 8 ∧ acceleratedOrbit 15 3569 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3569) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3569.1, data_15_3569.2]

/-- Complete interval computation for depth 15, residue 3570. -/
theorem bounds_15_3570 : exactInterval 15 3570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3570 : oddCount 3570 15 = 6 ∧ acceleratedOrbit 15 3570 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3570) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3570.1, data_15_3570.2]

end Collatz.Research.PassageAtlas.Batch0109
