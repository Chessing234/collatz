import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0036

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 537. -/
theorem bounds_10_537 : exactInterval 10 537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_537 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 537) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_537 : oddCount 537 10 = 5 ∧ acceleratedOrbit 10 537 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_537 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 537) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_537.1, data_10_537.2]

/-- Complete interval computation for depth 10, residue 538. -/
theorem bounds_10_538 : exactInterval 10 538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_538 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 538) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_538 : oddCount 538 10 = 4 ∧ acceleratedOrbit 10 538 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_538 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 538) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_538.1, data_10_538.2]

/-- Complete interval computation for depth 10, residue 539. -/
theorem bounds_10_539 : exactInterval 10 539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_539 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 539) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_539 : oddCount 539 10 = 7 ∧ acceleratedOrbit 10 539 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_539 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 539) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_539.1, data_10_539.2]

/-- Complete interval computation for depth 10, residue 540. -/
theorem bounds_10_540 : exactInterval 10 540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_540 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 540) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_540 : oddCount 540 10 = 4 ∧ acceleratedOrbit 10 540 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_540 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 540) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_540.1, data_10_540.2]

/-- Complete interval computation for depth 10, residue 541. -/
theorem bounds_10_541 : exactInterval 10 541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_541 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 541) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_541 : oddCount 541 10 = 4 ∧ acceleratedOrbit 10 541 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_541 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 541) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_541.1, data_10_541.2]

/-- Complete interval computation for depth 10, residue 542. -/
theorem bounds_10_542 : exactInterval 10 542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_542 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 542) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_542 : oddCount 542 10 = 4 ∧ acceleratedOrbit 10 542 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_542 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 542) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_542.1, data_10_542.2]

/-- Complete interval computation for depth 10, residue 543. -/
theorem bounds_10_543 : exactInterval 10 543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_543 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 543) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_543 : oddCount 543 10 = 7 ∧ acceleratedOrbit 10 543 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_543 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 543) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_543.1, data_10_543.2]

/-- Complete interval computation for depth 10, residue 544. -/
theorem bounds_10_544 : exactInterval 10 544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_544 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 544) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_544 : oddCount 544 10 = 2 ∧ acceleratedOrbit 10 544 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_544 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 544) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_544.1, data_10_544.2]

/-- Complete interval computation for depth 10, residue 545. -/
theorem bounds_10_545 : exactInterval 10 545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_545 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 545) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_545 : oddCount 545 10 = 5 ∧ acceleratedOrbit 10 545 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_545 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 545) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_545.1, data_10_545.2]

/-- Complete interval computation for depth 10, residue 546. -/
theorem bounds_10_546 : exactInterval 10 546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_546 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 546) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_546 : oddCount 546 10 = 4 ∧ acceleratedOrbit 10 546 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_546 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 546) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_546.1, data_10_546.2]

/-- Complete interval computation for depth 10, residue 547. -/
theorem bounds_10_547 : exactInterval 10 547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_547 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 547) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_547 : oddCount 547 10 = 4 ∧ acceleratedOrbit 10 547 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_547 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 547) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_547.1, data_10_547.2]

/-- Complete interval computation for depth 10, residue 548. -/
theorem bounds_10_548 : exactInterval 10 548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_548 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 548) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_548 : oddCount 548 10 = 6 ∧ acceleratedOrbit 10 548 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_548 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 548) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_548.1, data_10_548.2]

/-- Complete interval computation for depth 10, residue 549. -/
theorem bounds_10_549 : exactInterval 10 549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_549 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 549) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_549 : oddCount 549 10 = 6 ∧ acceleratedOrbit 10 549 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_549 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 549) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_549.1, data_10_549.2]

/-- Complete interval computation for depth 10, residue 550. -/
theorem bounds_10_550 : exactInterval 10 550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_550 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 550) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_550 : oddCount 550 10 = 6 ∧ acceleratedOrbit 10 550 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_550 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 550) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_550.1, data_10_550.2]

/-- Complete interval computation for depth 10, residue 551. -/
theorem bounds_10_551 : exactInterval 10 551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_551 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 551) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_551 : oddCount 551 10 = 5 ∧ acceleratedOrbit 10 551 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_551 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 551) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_551.1, data_10_551.2]

end Collatz.Research.StoppingAtlas.Batch0036
