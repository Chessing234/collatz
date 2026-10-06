import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0628

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20545. -/
theorem bounds_15_20545 : exactInterval 15 20545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20545 : oddCount 20545 15 = 7 ∧ acceleratedOrbit 15 20545 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20545) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20545.1, data_15_20545.2]

/-- Complete interval computation for depth 15, residue 20546. -/
theorem bounds_15_20546 : exactInterval 15 20546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20546 : oddCount 20546 15 = 7 ∧ acceleratedOrbit 15 20546 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20546) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20546.1, data_15_20546.2]

/-- Complete interval computation for depth 15, residue 20547. -/
theorem bounds_15_20547 : exactInterval 15 20547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20547 : oddCount 20547 15 = 7 ∧ acceleratedOrbit 15 20547 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20547) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20547.1, data_15_20547.2]

/-- Complete interval computation for depth 15, residue 20548. -/
theorem bounds_15_20548 : exactInterval 15 20548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20548 : oddCount 20548 15 = 7 ∧ acceleratedOrbit 15 20548 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20548) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20548.1, data_15_20548.2]

/-- Complete interval computation for depth 15, residue 20549. -/
theorem bounds_15_20549 : exactInterval 15 20549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20549 : oddCount 20549 15 = 7 ∧ acceleratedOrbit 15 20549 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20549) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20549.1, data_15_20549.2]

/-- Complete interval computation for depth 15, residue 20550. -/
theorem bounds_15_20550 : exactInterval 15 20550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20550 : oddCount 20550 15 = 7 ∧ acceleratedOrbit 15 20550 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20550) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20550.1, data_15_20550.2]

/-- Complete interval computation for depth 15, residue 20551. -/
theorem bounds_15_20551 : exactInterval 15 20551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20551 : oddCount 20551 15 = 10 ∧ acceleratedOrbit 15 20551 = 37037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20551) = 3 ^ 10 * m + 37037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20551.1, data_15_20551.2]

/-- Complete interval computation for depth 15, residue 20552. -/
theorem bounds_15_20552 : exactInterval 15 20552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20552 : oddCount 20552 15 = 6 ∧ acceleratedOrbit 15 20552 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20552) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20552.1, data_15_20552.2]

/-- Complete interval computation for depth 15, residue 20553. -/
theorem bounds_15_20553 : exactInterval 15 20553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20553 : oddCount 20553 15 = 10 ∧ acceleratedOrbit 15 20553 = 37043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20553) = 3 ^ 10 * m + 37043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20553.1, data_15_20553.2]

/-- Complete interval computation for depth 15, residue 20554. -/
theorem bounds_15_20554 : exactInterval 15 20554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20554 : oddCount 20554 15 = 6 ∧ acceleratedOrbit 15 20554 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20554) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20554.1, data_15_20554.2]

/-- Complete interval computation for depth 15, residue 20555. -/
theorem bounds_15_20555 : exactInterval 15 20555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20555 : oddCount 20555 15 = 7 ∧ acceleratedOrbit 15 20555 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20555) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20555.1, data_15_20555.2]

/-- Complete interval computation for depth 15, residue 20556. -/
theorem bounds_15_20556 : exactInterval 15 20556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20556 : oddCount 20556 15 = 6 ∧ acceleratedOrbit 15 20556 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20556) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20556.1, data_15_20556.2]

/-- Complete interval computation for depth 15, residue 20557. -/
theorem bounds_15_20557 : exactInterval 15 20557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20557 : oddCount 20557 15 = 6 ∧ acceleratedOrbit 15 20557 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20557) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20557.1, data_15_20557.2]

/-- Complete interval computation for depth 15, residue 20558. -/
theorem bounds_15_20558 : exactInterval 15 20558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20558 : oddCount 20558 15 = 9 ∧ acceleratedOrbit 15 20558 = 12352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20558) = 3 ^ 9 * m + 12352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20558.1, data_15_20558.2]

/-- Complete interval computation for depth 15, residue 20559. -/
theorem bounds_15_20559 : exactInterval 15 20559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20559 : oddCount 20559 15 = 9 ∧ acceleratedOrbit 15 20559 = 12352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20559) = 3 ^ 9 * m + 12352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20559.1, data_15_20559.2]

/-- Complete interval computation for depth 15, residue 20560. -/
theorem bounds_15_20560 : exactInterval 15 20560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20560 : oddCount 20560 15 = 3 ∧ acceleratedOrbit 15 20560 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20560) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20560.1, data_15_20560.2]

/-- Complete interval computation for depth 15, residue 20561. -/
theorem bounds_15_20561 : exactInterval 15 20561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20561 : oddCount 20561 15 = 6 ∧ acceleratedOrbit 15 20561 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20561) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20561.1, data_15_20561.2]

/-- Complete interval computation for depth 15, residue 20562. -/
theorem bounds_15_20562 : exactInterval 15 20562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20562 : oddCount 20562 15 = 10 ∧ acceleratedOrbit 15 20562 = 37061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20562) = 3 ^ 10 * m + 37061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20562.1, data_15_20562.2]

/-- Complete interval computation for depth 15, residue 20563. -/
theorem bounds_15_20563 : exactInterval 15 20563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20563 : oddCount 20563 15 = 10 ∧ acceleratedOrbit 15 20563 = 37061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20563) = 3 ^ 10 * m + 37061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20563.1, data_15_20563.2]

/-- Complete interval computation for depth 15, residue 20564. -/
theorem bounds_15_20564 : exactInterval 15 20564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20564 : oddCount 20564 15 = 3 ∧ acceleratedOrbit 15 20564 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20564) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20564.1, data_15_20564.2]

/-- Complete interval computation for depth 15, residue 20565. -/
theorem bounds_15_20565 : exactInterval 15 20565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20565 : oddCount 20565 15 = 3 ∧ acceleratedOrbit 15 20565 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20565) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20565.1, data_15_20565.2]

/-- Complete interval computation for depth 15, residue 20566. -/
theorem bounds_15_20566 : exactInterval 15 20566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20566 : oddCount 20566 15 = 8 ∧ acceleratedOrbit 15 20566 = 4121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20566) = 3 ^ 8 * m + 4121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20566.1, data_15_20566.2]

/-- Complete interval computation for depth 15, residue 20567. -/
theorem bounds_15_20567 : exactInterval 15 20567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20567 : oddCount 20567 15 = 8 ∧ acceleratedOrbit 15 20567 = 4121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20567) = 3 ^ 8 * m + 4121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20567.1, data_15_20567.2]

/-- Complete interval computation for depth 15, residue 20568. -/
theorem bounds_15_20568 : exactInterval 15 20568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20568 : oddCount 20568 15 = 7 ∧ acceleratedOrbit 15 20568 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20568) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20568.1, data_15_20568.2]

/-- Complete interval computation for depth 15, residue 20569. -/
theorem bounds_15_20569 : exactInterval 15 20569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20569 : oddCount 20569 15 = 8 ∧ acceleratedOrbit 15 20569 = 4121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20569) = 3 ^ 8 * m + 4121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20569.1, data_15_20569.2]

/-- Complete interval computation for depth 15, residue 20570. -/
theorem bounds_15_20570 : exactInterval 15 20570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20570 : oddCount 20570 15 = 7 ∧ acceleratedOrbit 15 20570 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20570) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20570.1, data_15_20570.2]

/-- Complete interval computation for depth 15, residue 20571. -/
theorem bounds_15_20571 : exactInterval 15 20571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20571 : oddCount 20571 15 = 10 ∧ acceleratedOrbit 15 20571 = 37073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20571) = 3 ^ 10 * m + 37073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20571.1, data_15_20571.2]

/-- Complete interval computation for depth 15, residue 20572. -/
theorem bounds_15_20572 : exactInterval 15 20572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20572 : oddCount 20572 15 = 7 ∧ acceleratedOrbit 15 20572 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20572) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20572.1, data_15_20572.2]

/-- Complete interval computation for depth 15, residue 20573. -/
theorem bounds_15_20573 : exactInterval 15 20573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20573 : oddCount 20573 15 = 7 ∧ acceleratedOrbit 15 20573 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20573) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20573.1, data_15_20573.2]

/-- Complete interval computation for depth 15, residue 20574. -/
theorem bounds_15_20574 : exactInterval 15 20574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20574 : oddCount 20574 15 = 8 ∧ acceleratedOrbit 15 20574 = 4120 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20574) = 3 ^ 8 * m + 4120 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20574.1, data_15_20574.2]

/-- Complete interval computation for depth 15, residue 20575. -/
theorem bounds_15_20575 : exactInterval 15 20575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20575 : oddCount 20575 15 = 8 ∧ acceleratedOrbit 15 20575 = 4120 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20575) = 3 ^ 8 * m + 4120 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20575.1, data_15_20575.2]

/-- Complete interval computation for depth 15, residue 20576. -/
theorem bounds_15_20576 : exactInterval 15 20576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20576 : oddCount 20576 15 = 3 ∧ acceleratedOrbit 15 20576 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20576) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20576.1, data_15_20576.2]

/-- Complete interval computation for depth 15, residue 20577. -/
theorem bounds_15_20577 : exactInterval 15 20577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20577 : oddCount 20577 15 = 10 ∧ acceleratedOrbit 15 20577 = 37088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20577) = 3 ^ 10 * m + 37088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20577.1, data_15_20577.2]

end Collatz.Research.PassageAtlas.Batch0628
