import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0811

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26542. -/
theorem bounds_15_26542 : exactInterval 15 26542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26542 : oddCount 26542 15 = 9 ∧ acceleratedOrbit 15 26542 = 15947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26542) = 3 ^ 9 * m + 15947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26542.1, data_15_26542.2]

/-- Complete interval computation for depth 15, residue 26543. -/
theorem bounds_15_26543 : exactInterval 15 26543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26543 : oddCount 26543 15 = 9 ∧ acceleratedOrbit 15 26543 = 15947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26543) = 3 ^ 9 * m + 15947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26543.1, data_15_26543.2]

/-- Complete interval computation for depth 15, residue 26544. -/
theorem bounds_15_26544 : exactInterval 15 26544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26544 : oddCount 26544 15 = 5 ∧ acceleratedOrbit 15 26544 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26544) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26544.1, data_15_26544.2]

/-- Complete interval computation for depth 15, residue 26545. -/
theorem bounds_15_26545 : exactInterval 15 26545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26545 : oddCount 26545 15 = 6 ∧ acceleratedOrbit 15 26545 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26545) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26545.1, data_15_26545.2]

/-- Complete interval computation for depth 15, residue 26546. -/
theorem bounds_15_26546 : exactInterval 15 26546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26546 : oddCount 26546 15 = 6 ∧ acceleratedOrbit 15 26546 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26546) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26546.1, data_15_26546.2]

/-- Complete interval computation for depth 15, residue 26547. -/
theorem bounds_15_26547 : exactInterval 15 26547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26547 : oddCount 26547 15 = 6 ∧ acceleratedOrbit 15 26547 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26547) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26547.1, data_15_26547.2]

/-- Complete interval computation for depth 15, residue 26548. -/
theorem bounds_15_26548 : exactInterval 15 26548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26548 : oddCount 26548 15 = 5 ∧ acceleratedOrbit 15 26548 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26548) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26548.1, data_15_26548.2]

/-- Complete interval computation for depth 15, residue 26549. -/
theorem bounds_15_26549 : exactInterval 15 26549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26549 : oddCount 26549 15 = 5 ∧ acceleratedOrbit 15 26549 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26549) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26549.1, data_15_26549.2]

/-- Complete interval computation for depth 15, residue 26550. -/
theorem bounds_15_26550 : exactInterval 15 26550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26550 : oddCount 26550 15 = 8 ∧ acceleratedOrbit 15 26550 = 5318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26550) = 3 ^ 8 * m + 5318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26550.1, data_15_26550.2]

/-- Complete interval computation for depth 15, residue 26551. -/
theorem bounds_15_26551 : exactInterval 15 26551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26551 : oddCount 26551 15 = 8 ∧ acceleratedOrbit 15 26551 = 5318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26551) = 3 ^ 8 * m + 5318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26551.1, data_15_26551.2]

/-- Complete interval computation for depth 15, residue 26552. -/
theorem bounds_15_26552 : exactInterval 15 26552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26552 : oddCount 26552 15 = 5 ∧ acceleratedOrbit 15 26552 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26552) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26552.1, data_15_26552.2]

/-- Complete interval computation for depth 15, residue 26553. -/
theorem bounds_15_26553 : exactInterval 15 26553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26553 : oddCount 26553 15 = 9 ∧ acceleratedOrbit 15 26553 = 15956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26553) = 3 ^ 9 * m + 15956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26553.1, data_15_26553.2]

/-- Complete interval computation for depth 15, residue 26554. -/
theorem bounds_15_26554 : exactInterval 15 26554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26554 : oddCount 26554 15 = 5 ∧ acceleratedOrbit 15 26554 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26554) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26554.1, data_15_26554.2]

/-- Complete interval computation for depth 15, residue 26555. -/
theorem bounds_15_26555 : exactInterval 15 26555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26555 : oddCount 26555 15 = 9 ∧ acceleratedOrbit 15 26555 = 15956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26555) = 3 ^ 9 * m + 15956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26555.1, data_15_26555.2]

/-- Complete interval computation for depth 15, residue 26556. -/
theorem bounds_15_26556 : exactInterval 15 26556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26556 : oddCount 26556 15 = 10 ∧ acceleratedOrbit 15 26556 = 47864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26556) = 3 ^ 10 * m + 47864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26556.1, data_15_26556.2]

/-- Complete interval computation for depth 15, residue 26557. -/
theorem bounds_15_26557 : exactInterval 15 26557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26557 : oddCount 26557 15 = 10 ∧ acceleratedOrbit 15 26557 = 47864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26557) = 3 ^ 10 * m + 47864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26557.1, data_15_26557.2]

/-- Complete interval computation for depth 15, residue 26558. -/
theorem bounds_15_26558 : exactInterval 15 26558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26558 : oddCount 26558 15 = 10 ∧ acceleratedOrbit 15 26558 = 47864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26558) = 3 ^ 10 * m + 47864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26558.1, data_15_26558.2]

/-- Complete interval computation for depth 15, residue 26559. -/
theorem bounds_15_26559 : exactInterval 15 26559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26559 : oddCount 26559 15 = 8 ∧ acceleratedOrbit 15 26559 = 5318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26559) = 3 ^ 8 * m + 5318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26559.1, data_15_26559.2]

/-- Complete interval computation for depth 15, residue 26560. -/
theorem bounds_15_26560 : exactInterval 15 26560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26560 : oddCount 26560 15 = 7 ∧ acceleratedOrbit 15 26560 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26560) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26560.1, data_15_26560.2]

/-- Complete interval computation for depth 15, residue 26561. -/
theorem bounds_15_26561 : exactInterval 15 26561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26561 : oddCount 26561 15 = 5 ∧ acceleratedOrbit 15 26561 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26561) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26561.1, data_15_26561.2]

/-- Complete interval computation for depth 15, residue 26562. -/
theorem bounds_15_26562 : exactInterval 15 26562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26562 : oddCount 26562 15 = 9 ∧ acceleratedOrbit 15 26562 = 15959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26562) = 3 ^ 9 * m + 15959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26562.1, data_15_26562.2]

/-- Complete interval computation for depth 15, residue 26563. -/
theorem bounds_15_26563 : exactInterval 15 26563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26563 : oddCount 26563 15 = 9 ∧ acceleratedOrbit 15 26563 = 15959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26563) = 3 ^ 9 * m + 15959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26563.1, data_15_26563.2]

/-- Complete interval computation for depth 15, residue 26564. -/
theorem bounds_15_26564 : exactInterval 15 26564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26564 : oddCount 26564 15 = 6 ∧ acceleratedOrbit 15 26564 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26564) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26564.1, data_15_26564.2]

/-- Complete interval computation for depth 15, residue 26565. -/
theorem bounds_15_26565 : exactInterval 15 26565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26565 : oddCount 26565 15 = 6 ∧ acceleratedOrbit 15 26565 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26565) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26565.1, data_15_26565.2]

/-- Complete interval computation for depth 15, residue 26566. -/
theorem bounds_15_26566 : exactInterval 15 26566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26566 : oddCount 26566 15 = 6 ∧ acceleratedOrbit 15 26566 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26566) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26566.1, data_15_26566.2]

/-- Complete interval computation for depth 15, residue 26567. -/
theorem bounds_15_26567 : exactInterval 15 26567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26567 : oddCount 26567 15 = 8 ∧ acceleratedOrbit 15 26567 = 5320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26567) = 3 ^ 8 * m + 5320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26567.1, data_15_26567.2]

/-- Complete interval computation for depth 15, residue 26568. -/
theorem bounds_15_26568 : exactInterval 15 26568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26568 : oddCount 26568 15 = 7 ∧ acceleratedOrbit 15 26568 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26568) = 3 ^ 7 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26568.1, data_15_26568.2]

/-- Complete interval computation for depth 15, residue 26569. -/
theorem bounds_15_26569 : exactInterval 15 26569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26569 : oddCount 26569 15 = 8 ∧ acceleratedOrbit 15 26569 = 5321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26569) = 3 ^ 8 * m + 5321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26569.1, data_15_26569.2]

/-- Complete interval computation for depth 15, residue 26570. -/
theorem bounds_15_26570 : exactInterval 15 26570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26570 : oddCount 26570 15 = 7 ∧ acceleratedOrbit 15 26570 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26570) = 3 ^ 7 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26570.1, data_15_26570.2]

/-- Complete interval computation for depth 15, residue 26571. -/
theorem bounds_15_26571 : exactInterval 15 26571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26571 : oddCount 26571 15 = 7 ∧ acceleratedOrbit 15 26571 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26571) = 3 ^ 7 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26571.1, data_15_26571.2]

/-- Complete interval computation for depth 15, residue 26572. -/
theorem bounds_15_26572 : exactInterval 15 26572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26572 : oddCount 26572 15 = 7 ∧ acceleratedOrbit 15 26572 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26572) = 3 ^ 7 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26572.1, data_15_26572.2]

/-- Complete interval computation for depth 15, residue 26573. -/
theorem bounds_15_26573 : exactInterval 15 26573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26573 : oddCount 26573 15 = 7 ∧ acceleratedOrbit 15 26573 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26573) = 3 ^ 7 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26573.1, data_15_26573.2]

end Collatz.Research.PassageAtlas.Batch0811
