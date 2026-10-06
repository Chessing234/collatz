import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0237

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 552. -/
theorem bounds_12_552 : exactInterval 12 552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_552 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 552) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_552 : oddCount 552 12 = 3 ∧ acceleratedOrbit 12 552 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_552 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 552) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_552.1, data_12_552.2]

/-- Complete interval computation for depth 12, residue 553. -/
theorem bounds_12_553 : exactInterval 12 553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_553 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 553) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_553 : oddCount 553 12 = 9 ∧ acceleratedOrbit 12 553 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_553 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 553) = 3 ^ 9 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_553.1, data_12_553.2]

/-- Complete interval computation for depth 12, residue 554. -/
theorem bounds_12_554 : exactInterval 12 554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_554 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 554) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_554 : oddCount 554 12 = 3 ∧ acceleratedOrbit 12 554 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_554 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 554) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_554.1, data_12_554.2]

/-- Complete interval computation for depth 12, residue 555. -/
theorem bounds_12_555 : exactInterval 12 555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_555 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 555) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_555 : oddCount 555 12 = 4 ∧ acceleratedOrbit 12 555 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_555 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 555) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_555.1, data_12_555.2]

/-- Complete interval computation for depth 12, residue 556. -/
theorem bounds_12_556 : exactInterval 12 556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_556 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 556) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_556 : oddCount 556 12 = 6 ∧ acceleratedOrbit 12 556 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_556 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 556) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_556.1, data_12_556.2]

/-- Complete interval computation for depth 12, residue 557. -/
theorem bounds_12_557 : exactInterval 12 557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_557 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 557) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_557 : oddCount 557 12 = 6 ∧ acceleratedOrbit 12 557 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_557 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 557) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_557.1, data_12_557.2]

/-- Complete interval computation for depth 12, residue 558. -/
theorem bounds_12_558 : exactInterval 12 558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_558 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 558) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_558 : oddCount 558 12 = 6 ∧ acceleratedOrbit 12 558 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_558 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 558) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_558.1, data_12_558.2]

/-- Complete interval computation for depth 12, residue 559. -/
theorem bounds_12_559 : exactInterval 12 559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_559 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 559) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_559 : oddCount 559 12 = 9 ∧ acceleratedOrbit 12 559 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_559 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 559) = 3 ^ 9 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_559.1, data_12_559.2]

/-- Complete interval computation for depth 12, residue 560. -/
theorem bounds_12_560 : exactInterval 12 560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_560 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 560) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_560 : oddCount 560 12 = 3 ∧ acceleratedOrbit 12 560 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_560 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 560) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_560.1, data_12_560.2]

/-- Complete interval computation for depth 12, residue 561. -/
theorem bounds_12_561 : exactInterval 12 561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_561 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 561) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_561 : oddCount 561 12 = 6 ∧ acceleratedOrbit 12 561 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_561 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 561) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_561.1, data_12_561.2]

/-- Complete interval computation for depth 12, residue 562. -/
theorem bounds_12_562 : exactInterval 12 562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_562 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 562) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_562 : oddCount 562 12 = 6 ∧ acceleratedOrbit 12 562 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_562 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 562) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_562.1, data_12_562.2]

/-- Complete interval computation for depth 12, residue 563. -/
theorem bounds_12_563 : exactInterval 12 563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_563 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 563) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_563 : oddCount 563 12 = 6 ∧ acceleratedOrbit 12 563 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_563 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 563) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_563.1, data_12_563.2]

/-- Complete interval computation for depth 12, residue 564. -/
theorem bounds_12_564 : exactInterval 12 564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_564 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 564) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_564 : oddCount 564 12 = 3 ∧ acceleratedOrbit 12 564 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_564 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 564) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_564.1, data_12_564.2]

/-- Complete interval computation for depth 12, residue 565. -/
theorem bounds_12_565 : exactInterval 12 565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_565 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 565) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_565 : oddCount 565 12 = 3 ∧ acceleratedOrbit 12 565 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_565 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 565) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_565.1, data_12_565.2]

/-- Complete interval computation for depth 12, residue 566. -/
theorem bounds_12_566 : exactInterval 12 566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_566 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 566) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_566 : oddCount 566 12 = 8 ∧ acceleratedOrbit 12 566 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_566 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 566) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_566.1, data_12_566.2]

/-- Complete interval computation for depth 12, residue 567. -/
theorem bounds_12_567 : exactInterval 12 567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_567 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 567) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_567 : oddCount 567 12 = 8 ∧ acceleratedOrbit 12 567 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_567 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 567) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_567.1, data_12_567.2]

end Collatz.Research.StoppingAtlas.Batch0237
