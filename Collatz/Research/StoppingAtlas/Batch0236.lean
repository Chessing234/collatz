import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0236

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 537. -/
theorem bounds_12_537 : exactInterval 12 537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_537 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 537) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_537 : oddCount 537 12 = 5 ∧ acceleratedOrbit 12 537 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_537 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 537) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_537.1, data_12_537.2]

/-- Complete interval computation for depth 12, residue 538. -/
theorem bounds_12_538 : exactInterval 12 538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_538 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 538) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_538 : oddCount 538 12 = 4 ∧ acceleratedOrbit 12 538 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_538 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 538) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_538.1, data_12_538.2]

/-- Complete interval computation for depth 12, residue 539. -/
theorem bounds_12_539 : exactInterval 12 539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_539 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 539) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_539 : oddCount 539 12 = 8 ∧ acceleratedOrbit 12 539 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_539 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 539) = 3 ^ 8 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_539.1, data_12_539.2]

/-- Complete interval computation for depth 12, residue 540. -/
theorem bounds_12_540 : exactInterval 12 540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_540 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 540) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_540 : oddCount 540 12 = 6 ∧ acceleratedOrbit 12 540 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_540 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 540) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_540.1, data_12_540.2]

/-- Complete interval computation for depth 12, residue 541. -/
theorem bounds_12_541 : exactInterval 12 541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_541 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 541) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_541 : oddCount 541 12 = 6 ∧ acceleratedOrbit 12 541 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_541 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 541) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_541.1, data_12_541.2]

/-- Complete interval computation for depth 12, residue 542. -/
theorem bounds_12_542 : exactInterval 12 542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_542 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 542) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_542 : oddCount 542 12 = 6 ∧ acceleratedOrbit 12 542 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_542 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 542) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_542.1, data_12_542.2]

/-- Complete interval computation for depth 12, residue 543. -/
theorem bounds_12_543 : exactInterval 12 543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_543 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 543) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_543 : oddCount 543 12 = 8 ∧ acceleratedOrbit 12 543 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_543 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 543) = 3 ^ 8 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_543.1, data_12_543.2]

/-- Complete interval computation for depth 12, residue 544. -/
theorem bounds_12_544 : exactInterval 12 544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_544 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 544) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_544 : oddCount 544 12 = 3 ∧ acceleratedOrbit 12 544 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_544 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 544) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_544.1, data_12_544.2]

/-- Complete interval computation for depth 12, residue 545. -/
theorem bounds_12_545 : exactInterval 12 545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_545 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 545) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_545 : oddCount 545 12 = 6 ∧ acceleratedOrbit 12 545 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_545 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 545) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_545.1, data_12_545.2]

/-- Complete interval computation for depth 12, residue 546. -/
theorem bounds_12_546 : exactInterval 12 546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_546 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 546) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_546 : oddCount 546 12 = 4 ∧ acceleratedOrbit 12 546 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_546 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 546) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_546.1, data_12_546.2]

/-- Complete interval computation for depth 12, residue 547. -/
theorem bounds_12_547 : exactInterval 12 547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_547 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 547) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_547 : oddCount 547 12 = 4 ∧ acceleratedOrbit 12 547 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_547 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 547) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_547.1, data_12_547.2]

/-- Complete interval computation for depth 12, residue 548. -/
theorem bounds_12_548 : exactInterval 12 548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_548 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 548) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_548 : oddCount 548 12 = 8 ∧ acceleratedOrbit 12 548 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_548 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 548) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_548.1, data_12_548.2]

/-- Complete interval computation for depth 12, residue 549. -/
theorem bounds_12_549 : exactInterval 12 549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_549 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 549) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_549 : oddCount 549 12 = 8 ∧ acceleratedOrbit 12 549 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_549 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 549) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_549.1, data_12_549.2]

/-- Complete interval computation for depth 12, residue 550. -/
theorem bounds_12_550 : exactInterval 12 550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_550 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 550) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_550 : oddCount 550 12 = 8 ∧ acceleratedOrbit 12 550 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_550 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 550) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_550.1, data_12_550.2]

/-- Complete interval computation for depth 12, residue 551. -/
theorem bounds_12_551 : exactInterval 12 551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_551 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 551) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_551 : oddCount 551 12 = 7 ∧ acceleratedOrbit 12 551 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_551 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 551) = 3 ^ 7 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_551.1, data_12_551.2]

end Collatz.Research.StoppingAtlas.Batch0236
