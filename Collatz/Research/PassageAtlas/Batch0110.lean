import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0110

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3571. -/
theorem bounds_15_3571 : exactInterval 15 3571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3571 : oddCount 3571 15 = 6 ∧ acceleratedOrbit 15 3571 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3571) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3571.1, data_15_3571.2]

/-- Complete interval computation for depth 15, residue 3572. -/
theorem bounds_15_3572 : exactInterval 15 3572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3572 : oddCount 3572 15 = 8 ∧ acceleratedOrbit 15 3572 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3572) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3572.1, data_15_3572.2]

/-- Complete interval computation for depth 15, residue 3573. -/
theorem bounds_15_3573 : exactInterval 15 3573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3573 : oddCount 3573 15 = 8 ∧ acceleratedOrbit 15 3573 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3573) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3573.1, data_15_3573.2]

/-- Complete interval computation for depth 15, residue 3574. -/
theorem bounds_15_3574 : exactInterval 15 3574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3574 : oddCount 3574 15 = 9 ∧ acceleratedOrbit 15 3574 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3574) = 3 ^ 9 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3574.1, data_15_3574.2]

/-- Complete interval computation for depth 15, residue 3575. -/
theorem bounds_15_3575 : exactInterval 15 3575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3575 : oddCount 3575 15 = 9 ∧ acceleratedOrbit 15 3575 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3575) = 3 ^ 9 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3575.1, data_15_3575.2]

/-- Complete interval computation for depth 15, residue 3576. -/
theorem bounds_15_3576 : exactInterval 15 3576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3576 : oddCount 3576 15 = 9 ∧ acceleratedOrbit 15 3576 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3576) = 3 ^ 9 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3576.1, data_15_3576.2]

/-- Complete interval computation for depth 15, residue 3577. -/
theorem bounds_15_3577 : exactInterval 15 3577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3577 : oddCount 3577 15 = 7 ∧ acceleratedOrbit 15 3577 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3577) = 3 ^ 7 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3577.1, data_15_3577.2]

/-- Complete interval computation for depth 15, residue 3578. -/
theorem bounds_15_3578 : exactInterval 15 3578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3578 : oddCount 3578 15 = 9 ∧ acceleratedOrbit 15 3578 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3578) = 3 ^ 9 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3578.1, data_15_3578.2]

/-- Complete interval computation for depth 15, residue 3579. -/
theorem bounds_15_3579 : exactInterval 15 3579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3579 : oddCount 3579 15 = 7 ∧ acceleratedOrbit 15 3579 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3579) = 3 ^ 7 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3579.1, data_15_3579.2]

/-- Complete interval computation for depth 15, residue 3580. -/
theorem bounds_15_3580 : exactInterval 15 3580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3580 : oddCount 3580 15 = 9 ∧ acceleratedOrbit 15 3580 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3580) = 3 ^ 9 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3580.1, data_15_3580.2]

/-- Complete interval computation for depth 15, residue 3581. -/
theorem bounds_15_3581 : exactInterval 15 3581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3581 : oddCount 3581 15 = 9 ∧ acceleratedOrbit 15 3581 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3581) = 3 ^ 9 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3581.1, data_15_3581.2]

/-- Complete interval computation for depth 15, residue 3582. -/
theorem bounds_15_3582 : exactInterval 15 3582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3582 : oddCount 3582 15 = 11 ∧ acceleratedOrbit 15 3582 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3582) = 3 ^ 11 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3582.1, data_15_3582.2]

/-- Complete interval computation for depth 15, residue 3583. -/
theorem bounds_15_3583 : exactInterval 15 3583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3583 : oddCount 3583 15 = 11 ∧ acceleratedOrbit 15 3583 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3583) = 3 ^ 11 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3583.1, data_15_3583.2]

/-- Complete interval computation for depth 15, residue 3584. -/
theorem bounds_15_3584 : exactInterval 15 3584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3584 : oddCount 3584 15 = 4 ∧ acceleratedOrbit 15 3584 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3584) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3584.1, data_15_3584.2]

/-- Complete interval computation for depth 15, residue 3585. -/
theorem bounds_15_3585 : exactInterval 15 3585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3585 : oddCount 3585 15 = 10 ∧ acceleratedOrbit 15 3585 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3585) = 3 ^ 10 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3585.1, data_15_3585.2]

/-- Complete interval computation for depth 15, residue 3586. -/
theorem bounds_15_3586 : exactInterval 15 3586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3586 : oddCount 3586 15 = 7 ∧ acceleratedOrbit 15 3586 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3586) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3586.1, data_15_3586.2]

/-- Complete interval computation for depth 15, residue 3587. -/
theorem bounds_15_3587 : exactInterval 15 3587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3587 : oddCount 3587 15 = 7 ∧ acceleratedOrbit 15 3587 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3587) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3587.1, data_15_3587.2]

/-- Complete interval computation for depth 15, residue 3588. -/
theorem bounds_15_3588 : exactInterval 15 3588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3588 : oddCount 3588 15 = 8 ∧ acceleratedOrbit 15 3588 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3588) = 3 ^ 8 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3588.1, data_15_3588.2]

/-- Complete interval computation for depth 15, residue 3589. -/
theorem bounds_15_3589 : exactInterval 15 3589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3589 : oddCount 3589 15 = 8 ∧ acceleratedOrbit 15 3589 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3589) = 3 ^ 8 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3589.1, data_15_3589.2]

/-- Complete interval computation for depth 15, residue 3590. -/
theorem bounds_15_3590 : exactInterval 15 3590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3590 : oddCount 3590 15 = 8 ∧ acceleratedOrbit 15 3590 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3590) = 3 ^ 8 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3590.1, data_15_3590.2]

/-- Complete interval computation for depth 15, residue 3591. -/
theorem bounds_15_3591 : exactInterval 15 3591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3591 : oddCount 3591 15 = 10 ∧ acceleratedOrbit 15 3591 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3591) = 3 ^ 10 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3591.1, data_15_3591.2]

/-- Complete interval computation for depth 15, residue 3592. -/
theorem bounds_15_3592 : exactInterval 15 3592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3592 : oddCount 3592 15 = 8 ∧ acceleratedOrbit 15 3592 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3592) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3592.1, data_15_3592.2]

/-- Complete interval computation for depth 15, residue 3593. -/
theorem bounds_15_3593 : exactInterval 15 3593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3593 : oddCount 3593 15 = 6 ∧ acceleratedOrbit 15 3593 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3593) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3593.1, data_15_3593.2]

/-- Complete interval computation for depth 15, residue 3594. -/
theorem bounds_15_3594 : exactInterval 15 3594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3594 : oddCount 3594 15 = 8 ∧ acceleratedOrbit 15 3594 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3594) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3594.1, data_15_3594.2]

/-- Complete interval computation for depth 15, residue 3595. -/
theorem bounds_15_3595 : exactInterval 15 3595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3595 : oddCount 3595 15 = 8 ∧ acceleratedOrbit 15 3595 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3595) = 3 ^ 8 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3595.1, data_15_3595.2]

/-- Complete interval computation for depth 15, residue 3596. -/
theorem bounds_15_3596 : exactInterval 15 3596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3596 : oddCount 3596 15 = 8 ∧ acceleratedOrbit 15 3596 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3596) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3596.1, data_15_3596.2]

/-- Complete interval computation for depth 15, residue 3597. -/
theorem bounds_15_3597 : exactInterval 15 3597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3597 : oddCount 3597 15 = 8 ∧ acceleratedOrbit 15 3597 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3597) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3597.1, data_15_3597.2]

/-- Complete interval computation for depth 15, residue 3598. -/
theorem bounds_15_3598 : exactInterval 15 3598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3598 : oddCount 3598 15 = 8 ∧ acceleratedOrbit 15 3598 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3598) = 3 ^ 8 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3598.1, data_15_3598.2]

/-- Complete interval computation for depth 15, residue 3599. -/
theorem bounds_15_3599 : exactInterval 15 3599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3599 : oddCount 3599 15 = 8 ∧ acceleratedOrbit 15 3599 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3599) = 3 ^ 8 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3599.1, data_15_3599.2]

/-- Complete interval computation for depth 15, residue 3600. -/
theorem bounds_15_3600 : exactInterval 15 3600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3600 : oddCount 3600 15 = 9 ∧ acceleratedOrbit 15 3600 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3600) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3600.1, data_15_3600.2]

/-- Complete interval computation for depth 15, residue 3601. -/
theorem bounds_15_3601 : exactInterval 15 3601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3601 : oddCount 3601 15 = 8 ∧ acceleratedOrbit 15 3601 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3601) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3601.1, data_15_3601.2]

/-- Complete interval computation for depth 15, residue 3602. -/
theorem bounds_15_3602 : exactInterval 15 3602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3602 : oddCount 3602 15 = 10 ∧ acceleratedOrbit 15 3602 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3602) = 3 ^ 10 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3602.1, data_15_3602.2]

/-- Complete interval computation for depth 15, residue 3603. -/
theorem bounds_15_3603 : exactInterval 15 3603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3603 : oddCount 3603 15 = 10 ∧ acceleratedOrbit 15 3603 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3603) = 3 ^ 10 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3603.1, data_15_3603.2]

end Collatz.Research.PassageAtlas.Batch0110
