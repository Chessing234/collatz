import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0764

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4551. -/
theorem bounds_13_4551 : exactInterval 13 4551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4551 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4551) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4551 : oddCount 4551 13 = 8 ∧ acceleratedOrbit 13 4551 = 3647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4551 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4551) = 3 ^ 8 * m + 3647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4551.1, data_13_4551.2]

/-- Complete interval computation for depth 13, residue 4552. -/
theorem bounds_13_4552 : exactInterval 13 4552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4552 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4552) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4552 : oddCount 4552 13 = 6 ∧ acceleratedOrbit 13 4552 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4552 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4552) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4552.1, data_13_4552.2]

/-- Complete interval computation for depth 13, residue 4553. -/
theorem bounds_13_4553 : exactInterval 13 4553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4553 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4553) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4553 : oddCount 4553 13 = 7 ∧ acceleratedOrbit 13 4553 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4553 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4553) = 3 ^ 7 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4553.1, data_13_4553.2]

/-- Complete interval computation for depth 13, residue 4554. -/
theorem bounds_13_4554 : exactInterval 13 4554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4554 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4554) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4554 : oddCount 4554 13 = 6 ∧ acceleratedOrbit 13 4554 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4554 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4554) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4554.1, data_13_4554.2]

/-- Complete interval computation for depth 13, residue 4555. -/
theorem bounds_13_4555 : exactInterval 13 4555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4555 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4555) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4555 : oddCount 4555 13 = 6 ∧ acceleratedOrbit 13 4555 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4555 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4555) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4555.1, data_13_4555.2]

/-- Complete interval computation for depth 13, residue 4556. -/
theorem bounds_13_4556 : exactInterval 13 4556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4556 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4556) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4556 : oddCount 4556 13 = 6 ∧ acceleratedOrbit 13 4556 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4556 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4556) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4556.1, data_13_4556.2]

/-- Complete interval computation for depth 13, residue 4557. -/
theorem bounds_13_4557 : exactInterval 13 4557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4557 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4557) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4557 : oddCount 4557 13 = 6 ∧ acceleratedOrbit 13 4557 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4557 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4557) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4557.1, data_13_4557.2]

/-- Complete interval computation for depth 13, residue 4558. -/
theorem bounds_13_4558 : exactInterval 13 4558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4558 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4558) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4558 : oddCount 4558 13 = 8 ∧ acceleratedOrbit 13 4558 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4558 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4558) = 3 ^ 8 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4558.1, data_13_4558.2]

/-- Complete interval computation for depth 13, residue 4559. -/
theorem bounds_13_4559 : exactInterval 13 4559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4559 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4559) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4559 : oddCount 4559 13 = 8 ∧ acceleratedOrbit 13 4559 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4559 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4559) = 3 ^ 8 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4559.1, data_13_4559.2]

/-- Complete interval computation for depth 13, residue 4560. -/
theorem bounds_13_4560 : exactInterval 13 4560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4560 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4560) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4560 : oddCount 4560 13 = 5 ∧ acceleratedOrbit 13 4560 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4560 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4560) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4560.1, data_13_4560.2]

/-- Complete interval computation for depth 13, residue 4561. -/
theorem bounds_13_4561 : exactInterval 13 4561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4561 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4561) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4561 : oddCount 4561 13 = 6 ∧ acceleratedOrbit 13 4561 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4561 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4561) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4561.1, data_13_4561.2]

/-- Complete interval computation for depth 13, residue 4562. -/
theorem bounds_13_4562 : exactInterval 13 4562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4562 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4562) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4562 : oddCount 4562 13 = 7 ∧ acceleratedOrbit 13 4562 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4562 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4562) = 3 ^ 7 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4562.1, data_13_4562.2]

/-- Complete interval computation for depth 13, residue 4563. -/
theorem bounds_13_4563 : exactInterval 13 4563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4563 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4563) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4563 : oddCount 4563 13 = 7 ∧ acceleratedOrbit 13 4563 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4563 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4563) = 3 ^ 7 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4563.1, data_13_4563.2]

/-- Complete interval computation for depth 13, residue 4564. -/
theorem bounds_13_4564 : exactInterval 13 4564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4564 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4564) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4564 : oddCount 4564 13 = 5 ∧ acceleratedOrbit 13 4564 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4564 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4564) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4564.1, data_13_4564.2]

/-- Complete interval computation for depth 13, residue 4565. -/
theorem bounds_13_4565 : exactInterval 13 4565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4565 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4565) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4565 : oddCount 4565 13 = 5 ∧ acceleratedOrbit 13 4565 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4565 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4565) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4565.1, data_13_4565.2]

/-- Complete interval computation for depth 13, residue 4566. -/
theorem bounds_13_4566 : exactInterval 13 4566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4566 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4566) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4566 : oddCount 4566 13 = 7 ∧ acceleratedOrbit 13 4566 = 1220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4566 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4566) = 3 ^ 7 * m + 1220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4566.1, data_13_4566.2]

end Collatz.Research.StoppingAtlas.Batch0764
