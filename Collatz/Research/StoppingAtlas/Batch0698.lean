import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0698

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3537. -/
theorem bounds_13_3537 : exactInterval 13 3537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3537 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3537) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3537 : oddCount 3537 13 = 4 ∧ acceleratedOrbit 13 3537 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3537 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3537) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3537.1, data_13_3537.2]

/-- Complete interval computation for depth 13, residue 3538. -/
theorem bounds_13_3538 : exactInterval 13 3538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3538 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3538) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3538 : oddCount 3538 13 = 8 ∧ acceleratedOrbit 13 3538 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3538 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3538) = 3 ^ 8 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3538.1, data_13_3538.2]

/-- Complete interval computation for depth 13, residue 3539. -/
theorem bounds_13_3539 : exactInterval 13 3539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3539 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3539) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3539 : oddCount 3539 13 = 8 ∧ acceleratedOrbit 13 3539 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3539 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3539) = 3 ^ 8 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3539.1, data_13_3539.2]

/-- Complete interval computation for depth 13, residue 3540. -/
theorem bounds_13_3540 : exactInterval 13 3540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3540 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3540) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3540 : oddCount 3540 13 = 5 ∧ acceleratedOrbit 13 3540 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3540 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3540) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3540.1, data_13_3540.2]

/-- Complete interval computation for depth 13, residue 3541. -/
theorem bounds_13_3541 : exactInterval 13 3541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3541 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3541) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3541 : oddCount 3541 13 = 5 ∧ acceleratedOrbit 13 3541 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3541 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3541) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3541.1, data_13_3541.2]

/-- Complete interval computation for depth 13, residue 3542. -/
theorem bounds_13_3542 : exactInterval 13 3542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3542 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3542) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3542 : oddCount 3542 13 = 7 ∧ acceleratedOrbit 13 3542 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3542 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3542) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3542.1, data_13_3542.2]

/-- Complete interval computation for depth 13, residue 3543. -/
theorem bounds_13_3543 : exactInterval 13 3543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3543 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3543) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3543 : oddCount 3543 13 = 7 ∧ acceleratedOrbit 13 3543 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3543 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3543) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3543.1, data_13_3543.2]

/-- Complete interval computation for depth 13, residue 3544. -/
theorem bounds_13_3544 : exactInterval 13 3544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3544 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3544) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3544 : oddCount 3544 13 = 6 ∧ acceleratedOrbit 13 3544 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3544 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3544) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3544.1, data_13_3544.2]

/-- Complete interval computation for depth 13, residue 3545. -/
theorem bounds_13_3545 : exactInterval 13 3545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3545 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3545) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3545 : oddCount 3545 13 = 6 ∧ acceleratedOrbit 13 3545 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3545 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3545) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3545.1, data_13_3545.2]

/-- Complete interval computation for depth 13, residue 3546. -/
theorem bounds_13_3546 : exactInterval 13 3546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3546 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3546) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3546 : oddCount 3546 13 = 6 ∧ acceleratedOrbit 13 3546 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3546 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3546) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3546.1, data_13_3546.2]

/-- Complete interval computation for depth 13, residue 3547. -/
theorem bounds_13_3547 : exactInterval 13 3547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3547 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3547) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3547 : oddCount 3547 13 = 6 ∧ acceleratedOrbit 13 3547 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3547 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3547) = 3 ^ 6 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3547.1, data_13_3547.2]

/-- Complete interval computation for depth 13, residue 3548. -/
theorem bounds_13_3548 : exactInterval 13 3548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3548 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3548) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3548 : oddCount 3548 13 = 6 ∧ acceleratedOrbit 13 3548 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3548 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3548) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3548.1, data_13_3548.2]

/-- Complete interval computation for depth 13, residue 3549. -/
theorem bounds_13_3549 : exactInterval 13 3549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3549 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3549) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3549 : oddCount 3549 13 = 6 ∧ acceleratedOrbit 13 3549 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3549 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3549) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3549.1, data_13_3549.2]

/-- Complete interval computation for depth 13, residue 3550. -/
theorem bounds_13_3550 : exactInterval 13 3550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3550 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3550) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3550 : oddCount 3550 13 = 8 ∧ acceleratedOrbit 13 3550 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3550 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3550) = 3 ^ 8 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3550.1, data_13_3550.2]

/-- Complete interval computation for depth 13, residue 3551. -/
theorem bounds_13_3551 : exactInterval 13 3551 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3551 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3551) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3551 : oddCount 3551 13 = 8 ∧ acceleratedOrbit 13 3551 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3551 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3551) = 3 ^ 8 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3551.1, data_13_3551.2]

/-- Complete interval computation for depth 13, residue 3552. -/
theorem bounds_13_3552 : exactInterval 13 3552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3552 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3552) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3552 : oddCount 3552 13 = 6 ∧ acceleratedOrbit 13 3552 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3552 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3552) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3552.1, data_13_3552.2]

end Collatz.Research.StoppingAtlas.Batch0698
