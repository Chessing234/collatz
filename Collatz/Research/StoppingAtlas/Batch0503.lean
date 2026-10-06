import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0503

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 542. -/
theorem bounds_13_542 : exactInterval 13 542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_542 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 542) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_542 : oddCount 542 13 = 6 ∧ acceleratedOrbit 13 542 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_542 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 542) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_542.1, data_13_542.2]

/-- Complete interval computation for depth 13, residue 543. -/
theorem bounds_13_543 : exactInterval 13 543 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_543 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 543) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_543 : oddCount 543 13 = 8 ∧ acceleratedOrbit 13 543 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_543 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 543) = 3 ^ 8 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_543.1, data_13_543.2]

/-- Complete interval computation for depth 13, residue 544. -/
theorem bounds_13_544 : exactInterval 13 544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_544 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 544) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_544 : oddCount 544 13 = 3 ∧ acceleratedOrbit 13 544 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_544 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 544) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_544.1, data_13_544.2]

/-- Complete interval computation for depth 13, residue 545. -/
theorem bounds_13_545 : exactInterval 13 545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_545 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 545) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_545 : oddCount 545 13 = 6 ∧ acceleratedOrbit 13 545 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_545 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 545) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_545.1, data_13_545.2]

/-- Complete interval computation for depth 13, residue 546. -/
theorem bounds_13_546 : exactInterval 13 546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_546 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 546) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_546 : oddCount 546 13 = 5 ∧ acceleratedOrbit 13 546 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_546 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 546) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_546.1, data_13_546.2]

/-- Complete interval computation for depth 13, residue 547. -/
theorem bounds_13_547 : exactInterval 13 547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_547 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 547) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_547 : oddCount 547 13 = 5 ∧ acceleratedOrbit 13 547 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_547 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 547) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_547.1, data_13_547.2]

/-- Complete interval computation for depth 13, residue 548. -/
theorem bounds_13_548 : exactInterval 13 548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_548 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 548) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_548 : oddCount 548 13 = 8 ∧ acceleratedOrbit 13 548 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_548 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 548) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_548.1, data_13_548.2]

/-- Complete interval computation for depth 13, residue 549. -/
theorem bounds_13_549 : exactInterval 13 549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_549 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 549) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_549 : oddCount 549 13 = 8 ∧ acceleratedOrbit 13 549 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_549 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 549) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_549.1, data_13_549.2]

/-- Complete interval computation for depth 13, residue 550. -/
theorem bounds_13_550 : exactInterval 13 550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_550 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 550) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_550 : oddCount 550 13 = 8 ∧ acceleratedOrbit 13 550 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_550 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 550) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_550.1, data_13_550.2]

/-- Complete interval computation for depth 13, residue 551. -/
theorem bounds_13_551 : exactInterval 13 551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_551 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 551) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_551 : oddCount 551 13 = 7 ∧ acceleratedOrbit 13 551 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_551 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 551) = 3 ^ 7 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_551.1, data_13_551.2]

/-- Complete interval computation for depth 13, residue 552. -/
theorem bounds_13_552 : exactInterval 13 552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_552 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 552) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_552 : oddCount 552 13 = 3 ∧ acceleratedOrbit 13 552 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_552 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 552) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_552.1, data_13_552.2]

/-- Complete interval computation for depth 13, residue 553. -/
theorem bounds_13_553 : exactInterval 13 553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_553 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 553) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_553 : oddCount 553 13 = 9 ∧ acceleratedOrbit 13 553 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_553 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 553) = 3 ^ 9 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_553.1, data_13_553.2]

/-- Complete interval computation for depth 13, residue 554. -/
theorem bounds_13_554 : exactInterval 13 554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_554 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 554) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_554 : oddCount 554 13 = 3 ∧ acceleratedOrbit 13 554 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_554 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 554) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_554.1, data_13_554.2]

/-- Complete interval computation for depth 13, residue 555. -/
theorem bounds_13_555 : exactInterval 13 555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_555 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 555) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_555 : oddCount 555 13 = 5 ∧ acceleratedOrbit 13 555 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_555 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 555) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_555.1, data_13_555.2]

/-- Complete interval computation for depth 13, residue 556. -/
theorem bounds_13_556 : exactInterval 13 556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_556 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 556) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_556 : oddCount 556 13 = 7 ∧ acceleratedOrbit 13 556 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_556 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 556) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_556.1, data_13_556.2]

/-- Complete interval computation for depth 13, residue 557. -/
theorem bounds_13_557 : exactInterval 13 557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_557 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 557) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_557 : oddCount 557 13 = 7 ∧ acceleratedOrbit 13 557 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_557 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 557) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_557.1, data_13_557.2]

end Collatz.Research.StoppingAtlas.Batch0503
