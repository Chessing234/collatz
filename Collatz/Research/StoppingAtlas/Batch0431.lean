import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0431

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3532. -/
theorem bounds_12_3532 : exactInterval 12 3532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3532 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3532) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3532 : oddCount 3532 12 = 4 ∧ acceleratedOrbit 12 3532 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3532 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3532) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3532.1, data_12_3532.2]

/-- Complete interval computation for depth 12, residue 3533. -/
theorem bounds_12_3533 : exactInterval 12 3533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3533 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3533) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3533 : oddCount 3533 12 = 4 ∧ acceleratedOrbit 12 3533 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3533 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3533) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3533.1, data_12_3533.2]

/-- Complete interval computation for depth 12, residue 3534. -/
theorem bounds_12_3534 : exactInterval 12 3534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3534 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3534) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3534 : oddCount 3534 12 = 8 ∧ acceleratedOrbit 12 3534 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3534 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3534) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3534.1, data_12_3534.2]

/-- Complete interval computation for depth 12, residue 3535. -/
theorem bounds_12_3535 : exactInterval 12 3535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3535 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3535) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3535 : oddCount 3535 12 = 8 ∧ acceleratedOrbit 12 3535 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3535 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3535) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3535.1, data_12_3535.2]

/-- Complete interval computation for depth 12, residue 3536. -/
theorem bounds_12_3536 : exactInterval 12 3536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3536 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3536) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3536 : oddCount 3536 12 = 4 ∧ acceleratedOrbit 12 3536 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3536 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3536) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3536.1, data_12_3536.2]

/-- Complete interval computation for depth 12, residue 3537. -/
theorem bounds_12_3537 : exactInterval 12 3537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3537 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3537) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3537 : oddCount 3537 12 = 4 ∧ acceleratedOrbit 12 3537 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3537 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3537) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3537.1, data_12_3537.2]

/-- Complete interval computation for depth 12, residue 3538. -/
theorem bounds_12_3538 : exactInterval 12 3538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3538 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3538) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3538 : oddCount 3538 12 = 7 ∧ acceleratedOrbit 12 3538 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3538 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3538) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3538.1, data_12_3538.2]

/-- Complete interval computation for depth 12, residue 3539. -/
theorem bounds_12_3539 : exactInterval 12 3539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3539 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3539) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3539 : oddCount 3539 12 = 7 ∧ acceleratedOrbit 12 3539 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3539 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3539) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3539.1, data_12_3539.2]

/-- Complete interval computation for depth 12, residue 3540. -/
theorem bounds_12_3540 : exactInterval 12 3540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3540 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3540) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3540 : oddCount 3540 12 = 4 ∧ acceleratedOrbit 12 3540 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3540 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3540) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3540.1, data_12_3540.2]

/-- Complete interval computation for depth 12, residue 3541. -/
theorem bounds_12_3541 : exactInterval 12 3541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3541 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3541) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3541 : oddCount 3541 12 = 4 ∧ acceleratedOrbit 12 3541 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3541 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3541) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3541.1, data_12_3541.2]

/-- Complete interval computation for depth 12, residue 3542. -/
theorem bounds_12_3542 : exactInterval 12 3542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3542 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3542) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3542 : oddCount 3542 12 = 6 ∧ acceleratedOrbit 12 3542 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3542 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3542) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3542.1, data_12_3542.2]

/-- Complete interval computation for depth 12, residue 3543. -/
theorem bounds_12_3543 : exactInterval 12 3543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3543 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3543) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3543 : oddCount 3543 12 = 6 ∧ acceleratedOrbit 12 3543 = 631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3543 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3543) = 3 ^ 6 * m + 631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3543.1, data_12_3543.2]

/-- Complete interval computation for depth 12, residue 3544. -/
theorem bounds_12_3544 : exactInterval 12 3544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3544 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3544) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3544 : oddCount 3544 12 = 5 ∧ acceleratedOrbit 12 3544 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3544 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3544) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3544.1, data_12_3544.2]

/-- Complete interval computation for depth 12, residue 3545. -/
theorem bounds_12_3545 : exactInterval 12 3545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3545 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3545) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3545 : oddCount 3545 12 = 5 ∧ acceleratedOrbit 12 3545 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3545 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3545) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3545.1, data_12_3545.2]

/-- Complete interval computation for depth 12, residue 3546. -/
theorem bounds_12_3546 : exactInterval 12 3546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3546 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3546) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3546 : oddCount 3546 12 = 5 ∧ acceleratedOrbit 12 3546 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3546 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3546) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3546.1, data_12_3546.2]

/-- Complete interval computation for depth 12, residue 3547. -/
theorem bounds_12_3547 : exactInterval 12 3547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3547 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3547) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3547 : oddCount 3547 12 = 6 ∧ acceleratedOrbit 12 3547 = 632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3547 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3547) = 3 ^ 6 * m + 632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3547.1, data_12_3547.2]

end Collatz.Research.StoppingAtlas.Batch0431
