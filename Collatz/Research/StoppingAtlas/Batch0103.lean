import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0103

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 542. -/
theorem bounds_11_542 : exactInterval 11 542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_542 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 542) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_542 : oddCount 542 11 = 5 ∧ acceleratedOrbit 11 542 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_542 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 542) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_542.1, data_11_542.2]

/-- Complete interval computation for depth 11, residue 543. -/
theorem bounds_11_543 : exactInterval 11 543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_543 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 543) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_543 : oddCount 543 11 = 7 ∧ acceleratedOrbit 11 543 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_543 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 543) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_543.1, data_11_543.2]

/-- Complete interval computation for depth 11, residue 544. -/
theorem bounds_11_544 : exactInterval 11 544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_544 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 544) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_544 : oddCount 544 11 = 3 ∧ acceleratedOrbit 11 544 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_544 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 544) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_544.1, data_11_544.2]

/-- Complete interval computation for depth 11, residue 545. -/
theorem bounds_11_545 : exactInterval 11 545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_545 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 545) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_545 : oddCount 545 11 = 5 ∧ acceleratedOrbit 11 545 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_545 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 545) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_545.1, data_11_545.2]

/-- Complete interval computation for depth 11, residue 546. -/
theorem bounds_11_546 : exactInterval 11 546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_546 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 546) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_546 : oddCount 546 11 = 4 ∧ acceleratedOrbit 11 546 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_546 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 546) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_546.1, data_11_546.2]

/-- Complete interval computation for depth 11, residue 547. -/
theorem bounds_11_547 : exactInterval 11 547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_547 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 547) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_547 : oddCount 547 11 = 4 ∧ acceleratedOrbit 11 547 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_547 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 547) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_547.1, data_11_547.2]

/-- Complete interval computation for depth 11, residue 548. -/
theorem bounds_11_548 : exactInterval 11 548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_548 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 548) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_548 : oddCount 548 11 = 7 ∧ acceleratedOrbit 11 548 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_548 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 548) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_548.1, data_11_548.2]

/-- Complete interval computation for depth 11, residue 549. -/
theorem bounds_11_549 : exactInterval 11 549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_549 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 549) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_549 : oddCount 549 11 = 7 ∧ acceleratedOrbit 11 549 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_549 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 549) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_549.1, data_11_549.2]

/-- Complete interval computation for depth 11, residue 550. -/
theorem bounds_11_550 : exactInterval 11 550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_550 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 550) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_550 : oddCount 550 11 = 7 ∧ acceleratedOrbit 11 550 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_550 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 550) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_550.1, data_11_550.2]

/-- Complete interval computation for depth 11, residue 551. -/
theorem bounds_11_551 : exactInterval 11 551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_551 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 551) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_551 : oddCount 551 11 = 6 ∧ acceleratedOrbit 11 551 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_551 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 551) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_551.1, data_11_551.2]

/-- Complete interval computation for depth 11, residue 552. -/
theorem bounds_11_552 : exactInterval 11 552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_552 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 552) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_552 : oddCount 552 11 = 3 ∧ acceleratedOrbit 11 552 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_552 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 552) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_552.1, data_11_552.2]

/-- Complete interval computation for depth 11, residue 553. -/
theorem bounds_11_553 : exactInterval 11 553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_553 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 553) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_553 : oddCount 553 11 = 8 ∧ acceleratedOrbit 11 553 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_553 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 553) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_553.1, data_11_553.2]

/-- Complete interval computation for depth 11, residue 554. -/
theorem bounds_11_554 : exactInterval 11 554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_554 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 554) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_554 : oddCount 554 11 = 3 ∧ acceleratedOrbit 11 554 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_554 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 554) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_554.1, data_11_554.2]

/-- Complete interval computation for depth 11, residue 555. -/
theorem bounds_11_555 : exactInterval 11 555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_555 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 555) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_555 : oddCount 555 11 = 4 ∧ acceleratedOrbit 11 555 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_555 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 555) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_555.1, data_11_555.2]

/-- Complete interval computation for depth 11, residue 556. -/
theorem bounds_11_556 : exactInterval 11 556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_556 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 556) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_556 : oddCount 556 11 = 5 ∧ acceleratedOrbit 11 556 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_556 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 556) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_556.1, data_11_556.2]

/-- Complete interval computation for depth 11, residue 557. -/
theorem bounds_11_557 : exactInterval 11 557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_557 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 557) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_557 : oddCount 557 11 = 5 ∧ acceleratedOrbit 11 557 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_557 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 557) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_557.1, data_11_557.2]

end Collatz.Research.StoppingAtlas.Batch0103
