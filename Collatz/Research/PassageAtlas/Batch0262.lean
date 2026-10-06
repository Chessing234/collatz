import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0262

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8552. -/
theorem bounds_15_8552 : exactInterval 15 8552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8552 : oddCount 8552 15 = 5 ∧ acceleratedOrbit 15 8552 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8552) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8552.1, data_15_8552.2]

/-- Complete interval computation for depth 15, residue 8553. -/
theorem bounds_15_8553 : exactInterval 15 8553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8553 : oddCount 8553 15 = 8 ∧ acceleratedOrbit 15 8553 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8553) = 3 ^ 8 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8553.1, data_15_8553.2]

/-- Complete interval computation for depth 15, residue 8554. -/
theorem bounds_15_8554 : exactInterval 15 8554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8554 : oddCount 8554 15 = 5 ∧ acceleratedOrbit 15 8554 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8554) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8554.1, data_15_8554.2]

/-- Complete interval computation for depth 15, residue 8555. -/
theorem bounds_15_8555 : exactInterval 15 8555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8555 : oddCount 8555 15 = 8 ∧ acceleratedOrbit 15 8555 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8555) = 3 ^ 8 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8555.1, data_15_8555.2]

/-- Complete interval computation for depth 15, residue 8556. -/
theorem bounds_15_8556 : exactInterval 15 8556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8556 : oddCount 8556 15 = 10 ∧ acceleratedOrbit 15 8556 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8556) = 3 ^ 10 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8556.1, data_15_8556.2]

/-- Complete interval computation for depth 15, residue 8557. -/
theorem bounds_15_8557 : exactInterval 15 8557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8557 : oddCount 8557 15 = 10 ∧ acceleratedOrbit 15 8557 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8557) = 3 ^ 10 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8557.1, data_15_8557.2]

/-- Complete interval computation for depth 15, residue 8558. -/
theorem bounds_15_8558 : exactInterval 15 8558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8558 : oddCount 8558 15 = 10 ∧ acceleratedOrbit 15 8558 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8558) = 3 ^ 10 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8558.1, data_15_8558.2]

/-- Complete interval computation for depth 15, residue 8559. -/
theorem bounds_15_8559 : exactInterval 15 8559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8559 : oddCount 8559 15 = 9 ∧ acceleratedOrbit 15 8559 = 5143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8559) = 3 ^ 9 * m + 5143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8559.1, data_15_8559.2]

/-- Complete interval computation for depth 15, residue 8560. -/
theorem bounds_15_8560 : exactInterval 15 8560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8560 : oddCount 8560 15 = 5 ∧ acceleratedOrbit 15 8560 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8560) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8560.1, data_15_8560.2]

/-- Complete interval computation for depth 15, residue 8561. -/
theorem bounds_15_8561 : exactInterval 15 8561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8561 : oddCount 8561 15 = 5 ∧ acceleratedOrbit 15 8561 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8561) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8561.1, data_15_8561.2]

/-- Complete interval computation for depth 15, residue 8562. -/
theorem bounds_15_8562 : exactInterval 15 8562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8562 : oddCount 8562 15 = 7 ∧ acceleratedOrbit 15 8562 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8562) = 3 ^ 7 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8562.1, data_15_8562.2]

/-- Complete interval computation for depth 15, residue 8563. -/
theorem bounds_15_8563 : exactInterval 15 8563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8563 : oddCount 8563 15 = 7 ∧ acceleratedOrbit 15 8563 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8563) = 3 ^ 7 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8563.1, data_15_8563.2]

/-- Complete interval computation for depth 15, residue 8564. -/
theorem bounds_15_8564 : exactInterval 15 8564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8564 : oddCount 8564 15 = 5 ∧ acceleratedOrbit 15 8564 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8564) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8564.1, data_15_8564.2]

/-- Complete interval computation for depth 15, residue 8565. -/
theorem bounds_15_8565 : exactInterval 15 8565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8565 : oddCount 8565 15 = 5 ∧ acceleratedOrbit 15 8565 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8565) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8565.1, data_15_8565.2]

/-- Complete interval computation for depth 15, residue 8566. -/
theorem bounds_15_8566 : exactInterval 15 8566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8566 : oddCount 8566 15 = 7 ∧ acceleratedOrbit 15 8566 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8566) = 3 ^ 7 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8566.1, data_15_8566.2]

/-- Complete interval computation for depth 15, residue 8567. -/
theorem bounds_15_8567 : exactInterval 15 8567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8567 : oddCount 8567 15 = 7 ∧ acceleratedOrbit 15 8567 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8567) = 3 ^ 7 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8567.1, data_15_8567.2]

/-- Complete interval computation for depth 15, residue 8568. -/
theorem bounds_15_8568 : exactInterval 15 8568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8568 : oddCount 8568 15 = 8 ∧ acceleratedOrbit 15 8568 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8568) = 3 ^ 8 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8568.1, data_15_8568.2]

/-- Complete interval computation for depth 15, residue 8569. -/
theorem bounds_15_8569 : exactInterval 15 8569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8569 : oddCount 8569 15 = 10 ∧ acceleratedOrbit 15 8569 = 15446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8569) = 3 ^ 10 * m + 15446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8569.1, data_15_8569.2]

/-- Complete interval computation for depth 15, residue 8570. -/
theorem bounds_15_8570 : exactInterval 15 8570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8570 : oddCount 8570 15 = 8 ∧ acceleratedOrbit 15 8570 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8570) = 3 ^ 8 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8570.1, data_15_8570.2]

/-- Complete interval computation for depth 15, residue 8571. -/
theorem bounds_15_8571 : exactInterval 15 8571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8571 : oddCount 8571 15 = 9 ∧ acceleratedOrbit 15 8571 = 5150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8571) = 3 ^ 9 * m + 5150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8571.1, data_15_8571.2]

/-- Complete interval computation for depth 15, residue 8572. -/
theorem bounds_15_8572 : exactInterval 15 8572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8572 : oddCount 8572 15 = 8 ∧ acceleratedOrbit 15 8572 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8572) = 3 ^ 8 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8572.1, data_15_8572.2]

/-- Complete interval computation for depth 15, residue 8573. -/
theorem bounds_15_8573 : exactInterval 15 8573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8573 : oddCount 8573 15 = 8 ∧ acceleratedOrbit 15 8573 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8573) = 3 ^ 8 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8573.1, data_15_8573.2]

/-- Complete interval computation for depth 15, residue 8574. -/
theorem bounds_15_8574 : exactInterval 15 8574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8574 : oddCount 8574 15 = 9 ∧ acceleratedOrbit 15 8574 = 5152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8574) = 3 ^ 9 * m + 5152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8574.1, data_15_8574.2]

/-- Complete interval computation for depth 15, residue 8575. -/
theorem bounds_15_8575 : exactInterval 15 8575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8575 : oddCount 8575 15 = 9 ∧ acceleratedOrbit 15 8575 = 5152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8575) = 3 ^ 9 * m + 5152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8575.1, data_15_8575.2]

/-- Complete interval computation for depth 15, residue 8576. -/
theorem bounds_15_8576 : exactInterval 15 8576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8576 : oddCount 8576 15 = 4 ∧ acceleratedOrbit 15 8576 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8576) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8576.1, data_15_8576.2]

/-- Complete interval computation for depth 15, residue 8577. -/
theorem bounds_15_8577 : exactInterval 15 8577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8577 : oddCount 8577 15 = 6 ∧ acceleratedOrbit 15 8577 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8577) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8577.1, data_15_8577.2]

/-- Complete interval computation for depth 15, residue 8578. -/
theorem bounds_15_8578 : exactInterval 15 8578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8578 : oddCount 8578 15 = 8 ∧ acceleratedOrbit 15 8578 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8578) = 3 ^ 8 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8578.1, data_15_8578.2]

/-- Complete interval computation for depth 15, residue 8579. -/
theorem bounds_15_8579 : exactInterval 15 8579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8579 : oddCount 8579 15 = 8 ∧ acceleratedOrbit 15 8579 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8579) = 3 ^ 8 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8579.1, data_15_8579.2]

/-- Complete interval computation for depth 15, residue 8580. -/
theorem bounds_15_8580 : exactInterval 15 8580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8580 : oddCount 8580 15 = 8 ∧ acceleratedOrbit 15 8580 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8580) = 3 ^ 8 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8580.1, data_15_8580.2]

/-- Complete interval computation for depth 15, residue 8581. -/
theorem bounds_15_8581 : exactInterval 15 8581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8581 : oddCount 8581 15 = 8 ∧ acceleratedOrbit 15 8581 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8581) = 3 ^ 8 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8581.1, data_15_8581.2]

/-- Complete interval computation for depth 15, residue 8582. -/
theorem bounds_15_8582 : exactInterval 15 8582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8582 : oddCount 8582 15 = 8 ∧ acceleratedOrbit 15 8582 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8582) = 3 ^ 8 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8582.1, data_15_8582.2]

/-- Complete interval computation for depth 15, residue 8583. -/
theorem bounds_15_8583 : exactInterval 15 8583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8583 : oddCount 8583 15 = 8 ∧ acceleratedOrbit 15 8583 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8583) = 3 ^ 8 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8583.1, data_15_8583.2]

/-- Complete interval computation for depth 15, residue 8584. -/
theorem bounds_15_8584 : exactInterval 15 8584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8584 : oddCount 8584 15 = 5 ∧ acceleratedOrbit 15 8584 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8584) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8584.1, data_15_8584.2]

end Collatz.Research.PassageAtlas.Batch0262
