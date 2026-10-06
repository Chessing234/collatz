import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0386

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12615. -/
theorem bounds_15_12615 : exactInterval 15 12615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12615 : oddCount 12615 15 = 10 ∧ acceleratedOrbit 15 12615 = 22736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12615) = 3 ^ 10 * m + 22736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12615.1, data_15_12615.2]

/-- Complete interval computation for depth 15, residue 12616. -/
theorem bounds_15_12616 : exactInterval 15 12616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12616 : oddCount 12616 15 = 10 ∧ acceleratedOrbit 15 12616 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12616) = 3 ^ 10 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12616.1, data_15_12616.2]

/-- Complete interval computation for depth 15, residue 12617. -/
theorem bounds_15_12617 : exactInterval 15 12617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12617 : oddCount 12617 15 = 8 ∧ acceleratedOrbit 15 12617 = 2528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12617) = 3 ^ 8 * m + 2528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12617.1, data_15_12617.2]

/-- Complete interval computation for depth 15, residue 12618. -/
theorem bounds_15_12618 : exactInterval 15 12618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12618 : oddCount 12618 15 = 10 ∧ acceleratedOrbit 15 12618 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12618) = 3 ^ 10 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12618.1, data_15_12618.2]

/-- Complete interval computation for depth 15, residue 12619. -/
theorem bounds_15_12619 : exactInterval 15 12619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12619 : oddCount 12619 15 = 6 ∧ acceleratedOrbit 15 12619 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12619) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12619.1, data_15_12619.2]

/-- Complete interval computation for depth 15, residue 12620. -/
theorem bounds_15_12620 : exactInterval 15 12620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12620 : oddCount 12620 15 = 10 ∧ acceleratedOrbit 15 12620 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12620) = 3 ^ 10 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12620.1, data_15_12620.2]

/-- Complete interval computation for depth 15, residue 12621. -/
theorem bounds_15_12621 : exactInterval 15 12621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12621 : oddCount 12621 15 = 10 ∧ acceleratedOrbit 15 12621 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12621) = 3 ^ 10 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12621.1, data_15_12621.2]

/-- Complete interval computation for depth 15, residue 12622. -/
theorem bounds_15_12622 : exactInterval 15 12622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12622 : oddCount 12622 15 = 10 ∧ acceleratedOrbit 15 12622 = 22751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12622) = 3 ^ 10 * m + 22751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12622.1, data_15_12622.2]

/-- Complete interval computation for depth 15, residue 12623. -/
theorem bounds_15_12623 : exactInterval 15 12623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12623 : oddCount 12623 15 = 10 ∧ acceleratedOrbit 15 12623 = 22751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12623) = 3 ^ 10 * m + 22751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12623.1, data_15_12623.2]

/-- Complete interval computation for depth 15, residue 12624. -/
theorem bounds_15_12624 : exactInterval 15 12624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12624 : oddCount 12624 15 = 3 ∧ acceleratedOrbit 15 12624 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12624) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12624.1, data_15_12624.2]

/-- Complete interval computation for depth 15, residue 12625. -/
theorem bounds_15_12625 : exactInterval 15 12625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12625 : oddCount 12625 15 = 10 ∧ acceleratedOrbit 15 12625 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12625) = 3 ^ 10 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12625.1, data_15_12625.2]

/-- Complete interval computation for depth 15, residue 12626. -/
theorem bounds_15_12626 : exactInterval 15 12626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12626 : oddCount 12626 15 = 11 ∧ acceleratedOrbit 15 12626 = 68276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12626) = 3 ^ 11 * m + 68276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12626.1, data_15_12626.2]

/-- Complete interval computation for depth 15, residue 12627. -/
theorem bounds_15_12627 : exactInterval 15 12627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12627 : oddCount 12627 15 = 11 ∧ acceleratedOrbit 15 12627 = 68276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12627) = 3 ^ 11 * m + 68276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12627.1, data_15_12627.2]

/-- Complete interval computation for depth 15, residue 12628. -/
theorem bounds_15_12628 : exactInterval 15 12628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12628 : oddCount 12628 15 = 3 ∧ acceleratedOrbit 15 12628 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12628) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12628.1, data_15_12628.2]

/-- Complete interval computation for depth 15, residue 12629. -/
theorem bounds_15_12629 : exactInterval 15 12629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12629 : oddCount 12629 15 = 3 ∧ acceleratedOrbit 15 12629 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12629) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12629.1, data_15_12629.2]

/-- Complete interval computation for depth 15, residue 12630. -/
theorem bounds_15_12630 : exactInterval 15 12630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12630 : oddCount 12630 15 = 8 ∧ acceleratedOrbit 15 12630 = 2531 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12630) = 3 ^ 8 * m + 2531 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12630.1, data_15_12630.2]

/-- Complete interval computation for depth 15, residue 12631. -/
theorem bounds_15_12631 : exactInterval 15 12631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12631 : oddCount 12631 15 = 8 ∧ acceleratedOrbit 15 12631 = 2531 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12631) = 3 ^ 8 * m + 2531 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12631.1, data_15_12631.2]

/-- Complete interval computation for depth 15, residue 12632. -/
theorem bounds_15_12632 : exactInterval 15 12632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12632 : oddCount 12632 15 = 5 ∧ acceleratedOrbit 15 12632 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12632) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12632.1, data_15_12632.2]

/-- Complete interval computation for depth 15, residue 12633. -/
theorem bounds_15_12633 : exactInterval 15 12633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12633 : oddCount 12633 15 = 8 ∧ acceleratedOrbit 15 12633 = 2531 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12633) = 3 ^ 8 * m + 2531 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12633.1, data_15_12633.2]

/-- Complete interval computation for depth 15, residue 12634. -/
theorem bounds_15_12634 : exactInterval 15 12634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12634 : oddCount 12634 15 = 5 ∧ acceleratedOrbit 15 12634 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12634) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12634.1, data_15_12634.2]

/-- Complete interval computation for depth 15, residue 12635. -/
theorem bounds_15_12635 : exactInterval 15 12635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12635 : oddCount 12635 15 = 8 ∧ acceleratedOrbit 15 12635 = 2531 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12635) = 3 ^ 8 * m + 2531 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12635.1, data_15_12635.2]

/-- Complete interval computation for depth 15, residue 12636. -/
theorem bounds_15_12636 : exactInterval 15 12636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12636 : oddCount 12636 15 = 5 ∧ acceleratedOrbit 15 12636 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12636) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12636.1, data_15_12636.2]

/-- Complete interval computation for depth 15, residue 12637. -/
theorem bounds_15_12637 : exactInterval 15 12637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12637 : oddCount 12637 15 = 5 ∧ acceleratedOrbit 15 12637 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12637) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12637.1, data_15_12637.2]

/-- Complete interval computation for depth 15, residue 12638. -/
theorem bounds_15_12638 : exactInterval 15 12638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12638 : oddCount 12638 15 = 10 ∧ acceleratedOrbit 15 12638 = 22781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12638) = 3 ^ 10 * m + 22781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12638.1, data_15_12638.2]

/-- Complete interval computation for depth 15, residue 12639. -/
theorem bounds_15_12639 : exactInterval 15 12639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12639 : oddCount 12639 15 = 10 ∧ acceleratedOrbit 15 12639 = 22781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12639) = 3 ^ 10 * m + 22781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12639.1, data_15_12639.2]

/-- Complete interval computation for depth 15, residue 12640. -/
theorem bounds_15_12640 : exactInterval 15 12640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12640 : oddCount 12640 15 = 6 ∧ acceleratedOrbit 15 12640 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12640) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12640.1, data_15_12640.2]

/-- Complete interval computation for depth 15, residue 12641. -/
theorem bounds_15_12641 : exactInterval 15 12641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12641 : oddCount 12641 15 = 10 ∧ acceleratedOrbit 15 12641 = 22787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12641) = 3 ^ 10 * m + 22787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12641.1, data_15_12641.2]

/-- Complete interval computation for depth 15, residue 12642. -/
theorem bounds_15_12642 : exactInterval 15 12642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12642 : oddCount 12642 15 = 8 ∧ acceleratedOrbit 15 12642 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12642) = 3 ^ 8 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12642.1, data_15_12642.2]

/-- Complete interval computation for depth 15, residue 12643. -/
theorem bounds_15_12643 : exactInterval 15 12643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12643 : oddCount 12643 15 = 8 ∧ acceleratedOrbit 15 12643 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12643) = 3 ^ 8 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12643.1, data_15_12643.2]

/-- Complete interval computation for depth 15, residue 12644. -/
theorem bounds_15_12644 : exactInterval 15 12644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12644 : oddCount 12644 15 = 8 ∧ acceleratedOrbit 15 12644 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12644) = 3 ^ 8 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12644.1, data_15_12644.2]

/-- Complete interval computation for depth 15, residue 12645. -/
theorem bounds_15_12645 : exactInterval 15 12645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12645 : oddCount 12645 15 = 8 ∧ acceleratedOrbit 15 12645 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12645) = 3 ^ 8 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12645.1, data_15_12645.2]

/-- Complete interval computation for depth 15, residue 12646. -/
theorem bounds_15_12646 : exactInterval 15 12646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12646 : oddCount 12646 15 = 8 ∧ acceleratedOrbit 15 12646 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12646) = 3 ^ 8 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12646.1, data_15_12646.2]

/-- Complete interval computation for depth 15, residue 12647. -/
theorem bounds_15_12647 : exactInterval 15 12647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12647 : oddCount 12647 15 = 9 ∧ acceleratedOrbit 15 12647 = 7598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12647) = 3 ^ 9 * m + 7598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12647.1, data_15_12647.2]

end Collatz.Research.PassageAtlas.Batch0386
