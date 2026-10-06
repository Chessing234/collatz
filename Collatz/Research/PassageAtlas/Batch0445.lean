import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0445

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14548. -/
theorem bounds_15_14548 : exactInterval 15 14548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14548 : oddCount 14548 15 = 2 ∧ acceleratedOrbit 15 14548 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14548) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14548.1, data_15_14548.2]

/-- Complete interval computation for depth 15, residue 14549. -/
theorem bounds_15_14549 : exactInterval 15 14549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14549 : oddCount 14549 15 = 2 ∧ acceleratedOrbit 15 14549 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14549) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14549.1, data_15_14549.2]

/-- Complete interval computation for depth 15, residue 14550. -/
theorem bounds_15_14550 : exactInterval 15 14550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14550 : oddCount 14550 15 = 9 ∧ acceleratedOrbit 15 14550 = 8743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14550) = 3 ^ 9 * m + 8743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14550.1, data_15_14550.2]

/-- Complete interval computation for depth 15, residue 14551. -/
theorem bounds_15_14551 : exactInterval 15 14551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14551 : oddCount 14551 15 = 9 ∧ acceleratedOrbit 15 14551 = 8743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14551) = 3 ^ 9 * m + 8743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14551.1, data_15_14551.2]

/-- Complete interval computation for depth 15, residue 14552. -/
theorem bounds_15_14552 : exactInterval 15 14552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14552 : oddCount 14552 15 = 11 ∧ acceleratedOrbit 15 14552 = 78731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14552) = 3 ^ 11 * m + 78731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14552.1, data_15_14552.2]

/-- Complete interval computation for depth 15, residue 14553. -/
theorem bounds_15_14553 : exactInterval 15 14553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14553 : oddCount 14553 15 = 10 ∧ acceleratedOrbit 15 14553 = 26243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14553) = 3 ^ 10 * m + 26243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14553.1, data_15_14553.2]

/-- Complete interval computation for depth 15, residue 14554. -/
theorem bounds_15_14554 : exactInterval 15 14554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14554 : oddCount 14554 15 = 11 ∧ acceleratedOrbit 15 14554 = 78731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14554) = 3 ^ 11 * m + 78731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14554.1, data_15_14554.2]

/-- Complete interval computation for depth 15, residue 14555. -/
theorem bounds_15_14555 : exactInterval 15 14555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14555 : oddCount 14555 15 = 10 ∧ acceleratedOrbit 15 14555 = 26234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14555) = 3 ^ 10 * m + 26234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14555.1, data_15_14555.2]

/-- Complete interval computation for depth 15, residue 14556. -/
theorem bounds_15_14556 : exactInterval 15 14556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14556 : oddCount 14556 15 = 11 ∧ acceleratedOrbit 15 14556 = 78731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14556) = 3 ^ 11 * m + 78731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14556.1, data_15_14556.2]

/-- Complete interval computation for depth 15, residue 14557. -/
theorem bounds_15_14557 : exactInterval 15 14557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14557 : oddCount 14557 15 = 11 ∧ acceleratedOrbit 15 14557 = 78731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14557) = 3 ^ 11 * m + 78731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14557.1, data_15_14557.2]

/-- Complete interval computation for depth 15, residue 14558. -/
theorem bounds_15_14558 : exactInterval 15 14558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14558 : oddCount 14558 15 = 10 ∧ acceleratedOrbit 15 14558 = 26239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14558) = 3 ^ 10 * m + 26239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14558.1, data_15_14558.2]

/-- Complete interval computation for depth 15, residue 14559. -/
theorem bounds_15_14559 : exactInterval 15 14559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14559 : oddCount 14559 15 = 10 ∧ acceleratedOrbit 15 14559 = 26239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14559) = 3 ^ 10 * m + 26239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14559.1, data_15_14559.2]

/-- Complete interval computation for depth 15, residue 14560. -/
theorem bounds_15_14560 : exactInterval 15 14560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14560 : oddCount 14560 15 = 6 ∧ acceleratedOrbit 15 14560 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14560) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14560.1, data_15_14560.2]

/-- Complete interval computation for depth 15, residue 14561. -/
theorem bounds_15_14561 : exactInterval 15 14561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14561 : oddCount 14561 15 = 13 ∧ acceleratedOrbit 15 14561 = 708587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14561) = 3 ^ 13 * m + 708587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14561.1, data_15_14561.2]

/-- Complete interval computation for depth 15, residue 14562. -/
theorem bounds_15_14562 : exactInterval 15 14562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14562 : oddCount 14562 15 = 2 ∧ acceleratedOrbit 15 14562 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14562) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14562.1, data_15_14562.2]

/-- Complete interval computation for depth 15, residue 14563. -/
theorem bounds_15_14563 : exactInterval 15 14563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14563 : oddCount 14563 15 = 2 ∧ acceleratedOrbit 15 14563 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14563) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14563.1, data_15_14563.2]

/-- Complete interval computation for depth 15, residue 14564. -/
theorem bounds_15_14564 : exactInterval 15 14564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14564 : oddCount 14564 15 = 7 ∧ acceleratedOrbit 15 14564 = 973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14564) = 3 ^ 7 * m + 973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14564.1, data_15_14564.2]

/-- Complete interval computation for depth 15, residue 14565. -/
theorem bounds_15_14565 : exactInterval 15 14565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14565 : oddCount 14565 15 = 7 ∧ acceleratedOrbit 15 14565 = 973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14565) = 3 ^ 7 * m + 973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14565.1, data_15_14565.2]

/-- Complete interval computation for depth 15, residue 14566. -/
theorem bounds_15_14566 : exactInterval 15 14566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14566 : oddCount 14566 15 = 7 ∧ acceleratedOrbit 15 14566 = 973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14566) = 3 ^ 7 * m + 973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14566.1, data_15_14566.2]

/-- Complete interval computation for depth 15, residue 14567. -/
theorem bounds_15_14567 : exactInterval 15 14567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14567 : oddCount 14567 15 = 8 ∧ acceleratedOrbit 15 14567 = 2917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14567) = 3 ^ 8 * m + 2917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14567.1, data_15_14567.2]

/-- Complete interval computation for depth 15, residue 14568. -/
theorem bounds_15_14568 : exactInterval 15 14568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14568 : oddCount 14568 15 = 6 ∧ acceleratedOrbit 15 14568 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14568) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14568.1, data_15_14568.2]

/-- Complete interval computation for depth 15, residue 14569. -/
theorem bounds_15_14569 : exactInterval 15 14569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14569 : oddCount 14569 15 = 8 ∧ acceleratedOrbit 15 14569 = 2918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14569) = 3 ^ 8 * m + 2918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14569.1, data_15_14569.2]

/-- Complete interval computation for depth 15, residue 14570. -/
theorem bounds_15_14570 : exactInterval 15 14570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14570 : oddCount 14570 15 = 6 ∧ acceleratedOrbit 15 14570 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14570) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14570.1, data_15_14570.2]

/-- Complete interval computation for depth 15, residue 14571. -/
theorem bounds_15_14571 : exactInterval 15 14571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14571 : oddCount 14571 15 = 8 ∧ acceleratedOrbit 15 14571 = 2918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14571) = 3 ^ 8 * m + 2918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14571.1, data_15_14571.2]

/-- Complete interval computation for depth 15, residue 14572. -/
theorem bounds_15_14572 : exactInterval 15 14572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14572 : oddCount 14572 15 = 7 ∧ acceleratedOrbit 15 14572 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14572) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14572.1, data_15_14572.2]

/-- Complete interval computation for depth 15, residue 14573. -/
theorem bounds_15_14573 : exactInterval 15 14573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14573 : oddCount 14573 15 = 7 ∧ acceleratedOrbit 15 14573 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14573) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14573.1, data_15_14573.2]

/-- Complete interval computation for depth 15, residue 14574. -/
theorem bounds_15_14574 : exactInterval 15 14574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14574 : oddCount 14574 15 = 7 ∧ acceleratedOrbit 15 14574 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14574) = 3 ^ 7 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14574.1, data_15_14574.2]

/-- Complete interval computation for depth 15, residue 14575. -/
theorem bounds_15_14575 : exactInterval 15 14575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14575 : oddCount 14575 15 = 12 ∧ acceleratedOrbit 15 14575 = 236402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14575) = 3 ^ 12 * m + 236402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14575.1, data_15_14575.2]

/-- Complete interval computation for depth 15, residue 14576. -/
theorem bounds_15_14576 : exactInterval 15 14576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14576 : oddCount 14576 15 = 6 ∧ acceleratedOrbit 15 14576 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14576) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14576.1, data_15_14576.2]

/-- Complete interval computation for depth 15, residue 14577. -/
theorem bounds_15_14577 : exactInterval 15 14577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14577 : oddCount 14577 15 = 6 ∧ acceleratedOrbit 15 14577 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14577) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14577.1, data_15_14577.2]

/-- Complete interval computation for depth 15, residue 14578. -/
theorem bounds_15_14578 : exactInterval 15 14578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14578 : oddCount 14578 15 = 8 ∧ acceleratedOrbit 15 14578 = 2920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14578) = 3 ^ 8 * m + 2920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14578.1, data_15_14578.2]

/-- Complete interval computation for depth 15, residue 14579. -/
theorem bounds_15_14579 : exactInterval 15 14579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14579 : oddCount 14579 15 = 8 ∧ acceleratedOrbit 15 14579 = 2920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14579) = 3 ^ 8 * m + 2920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14579.1, data_15_14579.2]

/-- Complete interval computation for depth 15, residue 14580. -/
theorem bounds_15_14580 : exactInterval 15 14580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14580 : oddCount 14580 15 = 6 ∧ acceleratedOrbit 15 14580 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14580) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14580.1, data_15_14580.2]

end Collatz.Research.PassageAtlas.Batch0445
