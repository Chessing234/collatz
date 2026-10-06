import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0434

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3578. -/
theorem bounds_12_3578 : exactInterval 12 3578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3578 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3578) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3578 : oddCount 3578 12 = 8 ∧ acceleratedOrbit 12 3578 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3578 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3578) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3578.1, data_12_3578.2]

/-- Complete interval computation for depth 12, residue 3579. -/
theorem bounds_12_3579 : exactInterval 12 3579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3579 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3579) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3579 : oddCount 3579 12 = 7 ∧ acceleratedOrbit 12 3579 = 1912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3579 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3579) = 3 ^ 7 * m + 1912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3579.1, data_12_3579.2]

/-- Complete interval computation for depth 12, residue 3580. -/
theorem bounds_12_3580 : exactInterval 12 3580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3580 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3580) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3580 : oddCount 3580 12 = 8 ∧ acceleratedOrbit 12 3580 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3580 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3580) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3580.1, data_12_3580.2]

/-- Complete interval computation for depth 12, residue 3581. -/
theorem bounds_12_3581 : exactInterval 12 3581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3581 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3581) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3581 : oddCount 3581 12 = 8 ∧ acceleratedOrbit 12 3581 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3581 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3581) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3581.1, data_12_3581.2]

/-- Complete interval computation for depth 12, residue 3582. -/
theorem bounds_12_3582 : exactInterval 12 3582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3582 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3582) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3582 : oddCount 3582 12 = 10 ∧ acceleratedOrbit 12 3582 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3582 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3582) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3582.1, data_12_3582.2]

/-- Complete interval computation for depth 12, residue 3583. -/
theorem bounds_12_3583 : exactInterval 12 3583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3583 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3583) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3583 : oddCount 3583 12 = 10 ∧ acceleratedOrbit 12 3583 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3583 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3583) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3583.1, data_12_3583.2]

/-- Complete interval computation for depth 12, residue 3584. -/
theorem bounds_12_3584 : exactInterval 12 3584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3584 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3584) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3584 : oddCount 3584 12 = 3 ∧ acceleratedOrbit 12 3584 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3584 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3584) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3584.1, data_12_3584.2]

/-- Complete interval computation for depth 12, residue 3585. -/
theorem bounds_12_3585 : exactInterval 12 3585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3585 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3585) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3585 : oddCount 3585 12 = 8 ∧ acceleratedOrbit 12 3585 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3585 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3585) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3585.1, data_12_3585.2]

/-- Complete interval computation for depth 12, residue 3586. -/
theorem bounds_12_3586 : exactInterval 12 3586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3586 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3586) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3586 : oddCount 3586 12 = 4 ∧ acceleratedOrbit 12 3586 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3586 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3586) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3586.1, data_12_3586.2]

/-- Complete interval computation for depth 12, residue 3587. -/
theorem bounds_12_3587 : exactInterval 12 3587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3587 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3587) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3587 : oddCount 3587 12 = 4 ∧ acceleratedOrbit 12 3587 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3587 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3587) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3587.1, data_12_3587.2]

/-- Complete interval computation for depth 12, residue 3588. -/
theorem bounds_12_3588 : exactInterval 12 3588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3588 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3588) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3588 : oddCount 3588 12 = 6 ∧ acceleratedOrbit 12 3588 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3588 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3588) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3588.1, data_12_3588.2]

/-- Complete interval computation for depth 12, residue 3589. -/
theorem bounds_12_3589 : exactInterval 12 3589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3589 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3589) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3589 : oddCount 3589 12 = 6 ∧ acceleratedOrbit 12 3589 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3589 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3589) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3589.1, data_12_3589.2]

/-- Complete interval computation for depth 12, residue 3590. -/
theorem bounds_12_3590 : exactInterval 12 3590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3590 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3590) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3590 : oddCount 3590 12 = 6 ∧ acceleratedOrbit 12 3590 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3590 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3590) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3590.1, data_12_3590.2]

/-- Complete interval computation for depth 12, residue 3591. -/
theorem bounds_12_3591 : exactInterval 12 3591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3591 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3591) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3591 : oddCount 3591 12 = 7 ∧ acceleratedOrbit 12 3591 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3591 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3591) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3591.1, data_12_3591.2]

/-- Complete interval computation for depth 12, residue 3592. -/
theorem bounds_12_3592 : exactInterval 12 3592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3592 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3592) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3592 : oddCount 3592 12 = 5 ∧ acceleratedOrbit 12 3592 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3592 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3592) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3592.1, data_12_3592.2]

/-- Complete interval computation for depth 12, residue 3593. -/
theorem bounds_12_3593 : exactInterval 12 3593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3593 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3593) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3593 : oddCount 3593 12 = 6 ∧ acceleratedOrbit 12 3593 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3593 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3593) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3593.1, data_12_3593.2]

end Collatz.Research.StoppingAtlas.Batch0434
