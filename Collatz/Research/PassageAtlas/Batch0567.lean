import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0567

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18546. -/
theorem bounds_15_18546 : exactInterval 15 18546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18546 : oddCount 18546 15 = 8 ∧ acceleratedOrbit 15 18546 = 3716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18546) = 3 ^ 8 * m + 3716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18546.1, data_15_18546.2]

/-- Complete interval computation for depth 15, residue 18547. -/
theorem bounds_15_18547 : exactInterval 15 18547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18547 : oddCount 18547 15 = 8 ∧ acceleratedOrbit 15 18547 = 3716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18547) = 3 ^ 8 * m + 3716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18547.1, data_15_18547.2]

/-- Complete interval computation for depth 15, residue 18548. -/
theorem bounds_15_18548 : exactInterval 15 18548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18548 : oddCount 18548 15 = 7 ∧ acceleratedOrbit 15 18548 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18548) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18548.1, data_15_18548.2]

/-- Complete interval computation for depth 15, residue 18549. -/
theorem bounds_15_18549 : exactInterval 15 18549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18549 : oddCount 18549 15 = 7 ∧ acceleratedOrbit 15 18549 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18549) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18549.1, data_15_18549.2]

/-- Complete interval computation for depth 15, residue 18550. -/
theorem bounds_15_18550 : exactInterval 15 18550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18550 : oddCount 18550 15 = 8 ∧ acceleratedOrbit 15 18550 = 3716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18550) = 3 ^ 8 * m + 3716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18550.1, data_15_18550.2]

/-- Complete interval computation for depth 15, residue 18551. -/
theorem bounds_15_18551 : exactInterval 15 18551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18551 : oddCount 18551 15 = 8 ∧ acceleratedOrbit 15 18551 = 3716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18551) = 3 ^ 8 * m + 3716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18551.1, data_15_18551.2]

/-- Complete interval computation for depth 15, residue 18552. -/
theorem bounds_15_18552 : exactInterval 15 18552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18552 : oddCount 18552 15 = 7 ∧ acceleratedOrbit 15 18552 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18552) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18552.1, data_15_18552.2]

/-- Complete interval computation for depth 15, residue 18553. -/
theorem bounds_15_18553 : exactInterval 15 18553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18553 : oddCount 18553 15 = 9 ∧ acceleratedOrbit 15 18553 = 11146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18553) = 3 ^ 9 * m + 11146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18553.1, data_15_18553.2]

/-- Complete interval computation for depth 15, residue 18554. -/
theorem bounds_15_18554 : exactInterval 15 18554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18554 : oddCount 18554 15 = 7 ∧ acceleratedOrbit 15 18554 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18554) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18554.1, data_15_18554.2]

/-- Complete interval computation for depth 15, residue 18555. -/
theorem bounds_15_18555 : exactInterval 15 18555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18555 : oddCount 18555 15 = 10 ∧ acceleratedOrbit 15 18555 = 33443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18555) = 3 ^ 10 * m + 33443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18555.1, data_15_18555.2]

/-- Complete interval computation for depth 15, residue 18556. -/
theorem bounds_15_18556 : exactInterval 15 18556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18556 : oddCount 18556 15 = 9 ∧ acceleratedOrbit 15 18556 = 11150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18556) = 3 ^ 9 * m + 11150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18556.1, data_15_18556.2]

/-- Complete interval computation for depth 15, residue 18557. -/
theorem bounds_15_18557 : exactInterval 15 18557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18557 : oddCount 18557 15 = 9 ∧ acceleratedOrbit 15 18557 = 11150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18557) = 3 ^ 9 * m + 11150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18557.1, data_15_18557.2]

/-- Complete interval computation for depth 15, residue 18558. -/
theorem bounds_15_18558 : exactInterval 15 18558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18558 : oddCount 18558 15 = 9 ∧ acceleratedOrbit 15 18558 = 11150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18558) = 3 ^ 9 * m + 11150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18558.1, data_15_18558.2]

/-- Complete interval computation for depth 15, residue 18559. -/
theorem bounds_15_18559 : exactInterval 15 18559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18559 : oddCount 18559 15 = 10 ∧ acceleratedOrbit 15 18559 = 33446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18559) = 3 ^ 10 * m + 33446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18559.1, data_15_18559.2]

/-- Complete interval computation for depth 15, residue 18560. -/
theorem bounds_15_18560 : exactInterval 15 18560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18560 : oddCount 18560 15 = 4 ∧ acceleratedOrbit 15 18560 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18560) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18560.1, data_15_18560.2]

/-- Complete interval computation for depth 15, residue 18561. -/
theorem bounds_15_18561 : exactInterval 15 18561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18561 : oddCount 18561 15 = 6 ∧ acceleratedOrbit 15 18561 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18561) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18561.1, data_15_18561.2]

/-- Complete interval computation for depth 15, residue 18562. -/
theorem bounds_15_18562 : exactInterval 15 18562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18562 : oddCount 18562 15 = 7 ∧ acceleratedOrbit 15 18562 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18562) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18562.1, data_15_18562.2]

/-- Complete interval computation for depth 15, residue 18563. -/
theorem bounds_15_18563 : exactInterval 15 18563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18563 : oddCount 18563 15 = 7 ∧ acceleratedOrbit 15 18563 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18563) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18563.1, data_15_18563.2]

/-- Complete interval computation for depth 15, residue 18564. -/
theorem bounds_15_18564 : exactInterval 15 18564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18564 : oddCount 18564 15 = 7 ∧ acceleratedOrbit 15 18564 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18564) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18564.1, data_15_18564.2]

/-- Complete interval computation for depth 15, residue 18565. -/
theorem bounds_15_18565 : exactInterval 15 18565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18565 : oddCount 18565 15 = 7 ∧ acceleratedOrbit 15 18565 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18565) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18565.1, data_15_18565.2]

/-- Complete interval computation for depth 15, residue 18566. -/
theorem bounds_15_18566 : exactInterval 15 18566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18566 : oddCount 18566 15 = 7 ∧ acceleratedOrbit 15 18566 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18566) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18566.1, data_15_18566.2]

/-- Complete interval computation for depth 15, residue 18567. -/
theorem bounds_15_18567 : exactInterval 15 18567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18567 : oddCount 18567 15 = 8 ∧ acceleratedOrbit 15 18567 = 3719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18567) = 3 ^ 8 * m + 3719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18567.1, data_15_18567.2]

/-- Complete interval computation for depth 15, residue 18568. -/
theorem bounds_15_18568 : exactInterval 15 18568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18568 : oddCount 18568 15 = 4 ∧ acceleratedOrbit 15 18568 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18568) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18568.1, data_15_18568.2]

/-- Complete interval computation for depth 15, residue 18569. -/
theorem bounds_15_18569 : exactInterval 15 18569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18569 : oddCount 18569 15 = 10 ∧ acceleratedOrbit 15 18569 = 33466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18569) = 3 ^ 10 * m + 33466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18569.1, data_15_18569.2]

/-- Complete interval computation for depth 15, residue 18570. -/
theorem bounds_15_18570 : exactInterval 15 18570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18570 : oddCount 18570 15 = 4 ∧ acceleratedOrbit 15 18570 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18570) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18570.1, data_15_18570.2]

/-- Complete interval computation for depth 15, residue 18571. -/
theorem bounds_15_18571 : exactInterval 15 18571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18571 : oddCount 18571 15 = 10 ∧ acceleratedOrbit 15 18571 = 33473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18571) = 3 ^ 10 * m + 33473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18571.1, data_15_18571.2]

/-- Complete interval computation for depth 15, residue 18572. -/
theorem bounds_15_18572 : exactInterval 15 18572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18572 : oddCount 18572 15 = 4 ∧ acceleratedOrbit 15 18572 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18572) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18572.1, data_15_18572.2]

/-- Complete interval computation for depth 15, residue 18573. -/
theorem bounds_15_18573 : exactInterval 15 18573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18573 : oddCount 18573 15 = 4 ∧ acceleratedOrbit 15 18573 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18573) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18573.1, data_15_18573.2]

/-- Complete interval computation for depth 15, residue 18574. -/
theorem bounds_15_18574 : exactInterval 15 18574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18574 : oddCount 18574 15 = 10 ∧ acceleratedOrbit 15 18574 = 33479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18574) = 3 ^ 10 * m + 33479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18574.1, data_15_18574.2]

/-- Complete interval computation for depth 15, residue 18575. -/
theorem bounds_15_18575 : exactInterval 15 18575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18575 : oddCount 18575 15 = 10 ∧ acceleratedOrbit 15 18575 = 33479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18575) = 3 ^ 10 * m + 33479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18575.1, data_15_18575.2]

/-- Complete interval computation for depth 15, residue 18576. -/
theorem bounds_15_18576 : exactInterval 15 18576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18576 : oddCount 18576 15 = 9 ∧ acceleratedOrbit 15 18576 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18576) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18576.1, data_15_18576.2]

/-- Complete interval computation for depth 15, residue 18577. -/
theorem bounds_15_18577 : exactInterval 15 18577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18577 : oddCount 18577 15 = 8 ∧ acceleratedOrbit 15 18577 = 3721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18577) = 3 ^ 8 * m + 3721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18577.1, data_15_18577.2]

/-- Complete interval computation for depth 15, residue 18578. -/
theorem bounds_15_18578 : exactInterval 15 18578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18578 : oddCount 18578 15 = 8 ∧ acceleratedOrbit 15 18578 = 3721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18578) = 3 ^ 8 * m + 3721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18578.1, data_15_18578.2]

end Collatz.Research.PassageAtlas.Batch0567
