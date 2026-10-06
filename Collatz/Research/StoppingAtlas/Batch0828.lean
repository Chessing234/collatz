import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0828

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5534. -/
theorem bounds_13_5534 : exactInterval 13 5534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5534 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5534) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5534 : oddCount 5534 13 = 9 ∧ acceleratedOrbit 13 5534 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5534 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5534) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5534.1, data_13_5534.2]

/-- Complete interval computation for depth 13, residue 5535. -/
theorem bounds_13_5535 : exactInterval 13 5535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5535 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5535) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5535 : oddCount 5535 13 = 11 ∧ acceleratedOrbit 13 5535 = 119717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5535 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5535) = 3 ^ 11 * m + 119717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5535.1, data_13_5535.2]

/-- Complete interval computation for depth 13, residue 5536. -/
theorem bounds_13_5536 : exactInterval 13 5536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5536 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5536) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5536 : oddCount 5536 13 = 4 ∧ acceleratedOrbit 13 5536 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5536 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5536) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5536.1, data_13_5536.2]

/-- Complete interval computation for depth 13, residue 5537. -/
theorem bounds_13_5537 : exactInterval 13 5537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5537 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5537) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5537 : oddCount 5537 13 = 6 ∧ acceleratedOrbit 13 5537 = 493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5537 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5537) = 3 ^ 6 * m + 493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5537.1, data_13_5537.2]

/-- Complete interval computation for depth 13, residue 5538. -/
theorem bounds_13_5538 : exactInterval 13 5538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5538 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5538) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5538 : oddCount 5538 13 = 6 ∧ acceleratedOrbit 13 5538 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5538 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5538) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5538.1, data_13_5538.2]

/-- Complete interval computation for depth 13, residue 5539. -/
theorem bounds_13_5539 : exactInterval 13 5539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5539 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5539) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5539 : oddCount 5539 13 = 6 ∧ acceleratedOrbit 13 5539 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5539 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5539) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5539.1, data_13_5539.2]

/-- Complete interval computation for depth 13, residue 5540. -/
theorem bounds_13_5540 : exactInterval 13 5540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5540 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5540) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5540 : oddCount 5540 13 = 6 ∧ acceleratedOrbit 13 5540 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5540 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5540) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5540.1, data_13_5540.2]

/-- Complete interval computation for depth 13, residue 5541. -/
theorem bounds_13_5541 : exactInterval 13 5541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5541 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5541) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5541 : oddCount 5541 13 = 6 ∧ acceleratedOrbit 13 5541 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5541 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5541) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5541.1, data_13_5541.2]

/-- Complete interval computation for depth 13, residue 5542. -/
theorem bounds_13_5542 : exactInterval 13 5542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5542 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5542) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5542 : oddCount 5542 13 = 6 ∧ acceleratedOrbit 13 5542 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5542 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5542) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5542.1, data_13_5542.2]

/-- Complete interval computation for depth 13, residue 5543. -/
theorem bounds_13_5543 : exactInterval 13 5543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5543 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5543) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5543 : oddCount 5543 13 = 8 ∧ acceleratedOrbit 13 5543 = 4441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5543 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5543) = 3 ^ 8 * m + 4441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5543.1, data_13_5543.2]

/-- Complete interval computation for depth 13, residue 5544. -/
theorem bounds_13_5544 : exactInterval 13 5544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5544 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5544) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5544 : oddCount 5544 13 = 4 ∧ acceleratedOrbit 13 5544 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5544 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5544) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5544.1, data_13_5544.2]

/-- Complete interval computation for depth 13, residue 5545. -/
theorem bounds_13_5545 : exactInterval 13 5545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5545 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5545) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5545 : oddCount 5545 13 = 9 ∧ acceleratedOrbit 13 5545 = 13328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5545 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5545) = 3 ^ 9 * m + 13328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5545.1, data_13_5545.2]

/-- Complete interval computation for depth 13, residue 5546. -/
theorem bounds_13_5546 : exactInterval 13 5546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5546 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5546) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5546 : oddCount 5546 13 = 4 ∧ acceleratedOrbit 13 5546 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5546 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5546) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5546.1, data_13_5546.2]

/-- Complete interval computation for depth 13, residue 5547. -/
theorem bounds_13_5547 : exactInterval 13 5547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5547 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5547) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5547 : oddCount 5547 13 = 8 ∧ acceleratedOrbit 13 5547 = 4445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5547 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5547) = 3 ^ 8 * m + 4445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5547.1, data_13_5547.2]

/-- Complete interval computation for depth 13, residue 5548. -/
theorem bounds_13_5548 : exactInterval 13 5548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5548 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5548) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5548 : oddCount 5548 13 = 7 ∧ acceleratedOrbit 13 5548 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5548 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5548) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5548.1, data_13_5548.2]

/-- Complete interval computation for depth 13, residue 5549. -/
theorem bounds_13_5549 : exactInterval 13 5549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5549 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5549) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5549 : oddCount 5549 13 = 7 ∧ acceleratedOrbit 13 5549 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5549 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5549) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5549.1, data_13_5549.2]

end Collatz.Research.StoppingAtlas.Batch0828
