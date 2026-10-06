import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0037

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 552. -/
theorem bounds_10_552 : exactInterval 10 552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_552 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 552) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_552 : oddCount 552 10 = 2 ∧ acceleratedOrbit 10 552 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_552 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 552) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_552.1, data_10_552.2]

/-- Complete interval computation for depth 10, residue 553. -/
theorem bounds_10_553 : exactInterval 10 553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_553 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 553) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_553 : oddCount 553 10 = 8 ∧ acceleratedOrbit 10 553 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_553 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 553) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_553.1, data_10_553.2]

/-- Complete interval computation for depth 10, residue 554. -/
theorem bounds_10_554 : exactInterval 10 554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_554 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 554) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_554 : oddCount 554 10 = 2 ∧ acceleratedOrbit 10 554 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_554 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 554) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_554.1, data_10_554.2]

/-- Complete interval computation for depth 10, residue 555. -/
theorem bounds_10_555 : exactInterval 10 555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_555 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 555) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_555 : oddCount 555 10 = 4 ∧ acceleratedOrbit 10 555 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_555 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 555) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_555.1, data_10_555.2]

/-- Complete interval computation for depth 10, residue 556. -/
theorem bounds_10_556 : exactInterval 10 556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_556 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 556) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_556 : oddCount 556 10 = 5 ∧ acceleratedOrbit 10 556 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_556 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 556) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_556.1, data_10_556.2]

/-- Complete interval computation for depth 10, residue 557. -/
theorem bounds_10_557 : exactInterval 10 557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_557 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 557) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_557 : oddCount 557 10 = 5 ∧ acceleratedOrbit 10 557 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_557 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 557) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_557.1, data_10_557.2]

/-- Complete interval computation for depth 10, residue 558. -/
theorem bounds_10_558 : exactInterval 10 558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_558 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 558) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_558 : oddCount 558 10 = 5 ∧ acceleratedOrbit 10 558 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_558 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 558) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_558.1, data_10_558.2]

/-- Complete interval computation for depth 10, residue 559. -/
theorem bounds_10_559 : exactInterval 10 559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_559 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 559) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_559 : oddCount 559 10 = 8 ∧ acceleratedOrbit 10 559 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_559 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 559) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_559.1, data_10_559.2]

/-- Complete interval computation for depth 10, residue 560. -/
theorem bounds_10_560 : exactInterval 10 560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_560 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 560) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_560 : oddCount 560 10 = 2 ∧ acceleratedOrbit 10 560 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_560 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 560) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_560.1, data_10_560.2]

/-- Complete interval computation for depth 10, residue 561. -/
theorem bounds_10_561 : exactInterval 10 561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_561 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 561) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_561 : oddCount 561 10 = 6 ∧ acceleratedOrbit 10 561 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_561 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 561) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_561.1, data_10_561.2]

/-- Complete interval computation for depth 10, residue 562. -/
theorem bounds_10_562 : exactInterval 10 562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_562 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 562) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_562 : oddCount 562 10 = 6 ∧ acceleratedOrbit 10 562 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_562 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 562) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_562.1, data_10_562.2]

/-- Complete interval computation for depth 10, residue 563. -/
theorem bounds_10_563 : exactInterval 10 563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_563 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 563) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_563 : oddCount 563 10 = 6 ∧ acceleratedOrbit 10 563 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_563 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 563) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_563.1, data_10_563.2]

/-- Complete interval computation for depth 10, residue 564. -/
theorem bounds_10_564 : exactInterval 10 564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_564 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 564) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_564 : oddCount 564 10 = 2 ∧ acceleratedOrbit 10 564 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_564 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 564) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_564.1, data_10_564.2]

/-- Complete interval computation for depth 10, residue 565. -/
theorem bounds_10_565 : exactInterval 10 565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_565 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 565) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_565 : oddCount 565 10 = 2 ∧ acceleratedOrbit 10 565 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_565 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 565) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_565.1, data_10_565.2]

/-- Complete interval computation for depth 10, residue 566. -/
theorem bounds_10_566 : exactInterval 10 566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_566 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 566) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_566 : oddCount 566 10 = 8 ∧ acceleratedOrbit 10 566 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_566 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 566) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_566.1, data_10_566.2]

/-- Complete interval computation for depth 10, residue 567. -/
theorem bounds_10_567 : exactInterval 10 567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_567 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 567) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_567 : oddCount 567 10 = 8 ∧ acceleratedOrbit 10 567 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_567 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 567) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_567.1, data_10_567.2]

end Collatz.Research.StoppingAtlas.Batch0037
