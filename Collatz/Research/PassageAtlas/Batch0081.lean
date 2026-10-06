import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0081

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2621. -/
theorem bounds_15_2621 : exactInterval 15 2621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2621 : oddCount 2621 15 = 9 ∧ acceleratedOrbit 15 2621 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2621) = 3 ^ 9 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2621.1, data_15_2621.2]

/-- Complete interval computation for depth 15, residue 2622. -/
theorem bounds_15_2622 : exactInterval 15 2622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2622 : oddCount 2622 15 = 8 ∧ acceleratedOrbit 15 2622 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2622) = 3 ^ 8 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2622.1, data_15_2622.2]

/-- Complete interval computation for depth 15, residue 2623. -/
theorem bounds_15_2623 : exactInterval 15 2623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2623 : oddCount 2623 15 = 8 ∧ acceleratedOrbit 15 2623 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2623) = 3 ^ 8 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2623.1, data_15_2623.2]

/-- Complete interval computation for depth 15, residue 2624. -/
theorem bounds_15_2624 : exactInterval 15 2624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2624 : oddCount 2624 15 = 7 ∧ acceleratedOrbit 15 2624 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2624) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2624.1, data_15_2624.2]

/-- Complete interval computation for depth 15, residue 2625. -/
theorem bounds_15_2625 : exactInterval 15 2625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2625 : oddCount 2625 15 = 5 ∧ acceleratedOrbit 15 2625 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2625) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2625.1, data_15_2625.2]

/-- Complete interval computation for depth 15, residue 2626. -/
theorem bounds_15_2626 : exactInterval 15 2626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2626 : oddCount 2626 15 = 5 ∧ acceleratedOrbit 15 2626 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2626) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2626.1, data_15_2626.2]

/-- Complete interval computation for depth 15, residue 2627. -/
theorem bounds_15_2627 : exactInterval 15 2627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2627 : oddCount 2627 15 = 5 ∧ acceleratedOrbit 15 2627 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2627) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2627.1, data_15_2627.2]

/-- Complete interval computation for depth 15, residue 2628. -/
theorem bounds_15_2628 : exactInterval 15 2628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2628 : oddCount 2628 15 = 6 ∧ acceleratedOrbit 15 2628 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2628) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2628.1, data_15_2628.2]

/-- Complete interval computation for depth 15, residue 2629. -/
theorem bounds_15_2629 : exactInterval 15 2629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2629 : oddCount 2629 15 = 6 ∧ acceleratedOrbit 15 2629 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2629) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2629.1, data_15_2629.2]

/-- Complete interval computation for depth 15, residue 2630. -/
theorem bounds_15_2630 : exactInterval 15 2630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2630 : oddCount 2630 15 = 6 ∧ acceleratedOrbit 15 2630 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2630) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2630.1, data_15_2630.2]

/-- Complete interval computation for depth 15, residue 2631. -/
theorem bounds_15_2631 : exactInterval 15 2631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2631 : oddCount 2631 15 = 9 ∧ acceleratedOrbit 15 2631 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2631) = 3 ^ 9 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2631.1, data_15_2631.2]

/-- Complete interval computation for depth 15, residue 2632. -/
theorem bounds_15_2632 : exactInterval 15 2632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2632 : oddCount 2632 15 = 6 ∧ acceleratedOrbit 15 2632 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2632) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2632.1, data_15_2632.2]

/-- Complete interval computation for depth 15, residue 2633. -/
theorem bounds_15_2633 : exactInterval 15 2633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2633 : oddCount 2633 15 = 7 ∧ acceleratedOrbit 15 2633 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2633) = 3 ^ 7 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2633.1, data_15_2633.2]

/-- Complete interval computation for depth 15, residue 2634. -/
theorem bounds_15_2634 : exactInterval 15 2634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2634 : oddCount 2634 15 = 6 ∧ acceleratedOrbit 15 2634 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2634) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2634.1, data_15_2634.2]

/-- Complete interval computation for depth 15, residue 2635. -/
theorem bounds_15_2635 : exactInterval 15 2635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2635 : oddCount 2635 15 = 6 ∧ acceleratedOrbit 15 2635 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2635) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2635.1, data_15_2635.2]

/-- Complete interval computation for depth 15, residue 2636. -/
theorem bounds_15_2636 : exactInterval 15 2636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2636 : oddCount 2636 15 = 6 ∧ acceleratedOrbit 15 2636 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2636) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2636.1, data_15_2636.2]

/-- Complete interval computation for depth 15, residue 2637. -/
theorem bounds_15_2637 : exactInterval 15 2637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2637 : oddCount 2637 15 = 6 ∧ acceleratedOrbit 15 2637 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2637) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2637.1, data_15_2637.2]

/-- Complete interval computation for depth 15, residue 2638. -/
theorem bounds_15_2638 : exactInterval 15 2638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2638 : oddCount 2638 15 = 8 ∧ acceleratedOrbit 15 2638 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2638) = 3 ^ 8 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2638.1, data_15_2638.2]

/-- Complete interval computation for depth 15, residue 2639. -/
theorem bounds_15_2639 : exactInterval 15 2639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2639 : oddCount 2639 15 = 8 ∧ acceleratedOrbit 15 2639 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2639) = 3 ^ 8 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2639.1, data_15_2639.2]

/-- Complete interval computation for depth 15, residue 2640. -/
theorem bounds_15_2640 : exactInterval 15 2640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2640 : oddCount 2640 15 = 7 ∧ acceleratedOrbit 15 2640 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2640) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2640.1, data_15_2640.2]

/-- Complete interval computation for depth 15, residue 2641. -/
theorem bounds_15_2641 : exactInterval 15 2641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2641 : oddCount 2641 15 = 10 ∧ acceleratedOrbit 15 2641 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2641) = 3 ^ 10 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2641.1, data_15_2641.2]

/-- Complete interval computation for depth 15, residue 2642. -/
theorem bounds_15_2642 : exactInterval 15 2642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2642 : oddCount 2642 15 = 10 ∧ acceleratedOrbit 15 2642 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2642) = 3 ^ 10 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2642.1, data_15_2642.2]

/-- Complete interval computation for depth 15, residue 2643. -/
theorem bounds_15_2643 : exactInterval 15 2643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2643 : oddCount 2643 15 = 10 ∧ acceleratedOrbit 15 2643 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2643) = 3 ^ 10 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2643.1, data_15_2643.2]

/-- Complete interval computation for depth 15, residue 2644. -/
theorem bounds_15_2644 : exactInterval 15 2644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2644 : oddCount 2644 15 = 7 ∧ acceleratedOrbit 15 2644 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2644) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2644.1, data_15_2644.2]

/-- Complete interval computation for depth 15, residue 2645. -/
theorem bounds_15_2645 : exactInterval 15 2645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2645 : oddCount 2645 15 = 7 ∧ acceleratedOrbit 15 2645 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2645) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2645.1, data_15_2645.2]

/-- Complete interval computation for depth 15, residue 2646. -/
theorem bounds_15_2646 : exactInterval 15 2646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2646 : oddCount 2646 15 = 6 ∧ acceleratedOrbit 15 2646 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2646) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2646.1, data_15_2646.2]

/-- Complete interval computation for depth 15, residue 2647. -/
theorem bounds_15_2647 : exactInterval 15 2647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2647 : oddCount 2647 15 = 6 ∧ acceleratedOrbit 15 2647 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2647) = 3 ^ 6 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2647.1, data_15_2647.2]

/-- Complete interval computation for depth 15, residue 2648. -/
theorem bounds_15_2648 : exactInterval 15 2648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2648 : oddCount 2648 15 = 5 ∧ acceleratedOrbit 15 2648 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2648) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2648.1, data_15_2648.2]

/-- Complete interval computation for depth 15, residue 2649. -/
theorem bounds_15_2649 : exactInterval 15 2649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2649 : oddCount 2649 15 = 9 ∧ acceleratedOrbit 15 2649 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2649) = 3 ^ 9 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2649.1, data_15_2649.2]

/-- Complete interval computation for depth 15, residue 2650. -/
theorem bounds_15_2650 : exactInterval 15 2650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2650 : oddCount 2650 15 = 5 ∧ acceleratedOrbit 15 2650 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2650) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2650.1, data_15_2650.2]

/-- Complete interval computation for depth 15, residue 2651. -/
theorem bounds_15_2651 : exactInterval 15 2651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2651 : oddCount 2651 15 = 10 ∧ acceleratedOrbit 15 2651 = 4781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2651) = 3 ^ 10 * m + 4781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2651.1, data_15_2651.2]

/-- Complete interval computation for depth 15, residue 2652. -/
theorem bounds_15_2652 : exactInterval 15 2652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2652 : oddCount 2652 15 = 5 ∧ acceleratedOrbit 15 2652 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2652) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2652.1, data_15_2652.2]

/-- Complete interval computation for depth 15, residue 2653. -/
theorem bounds_15_2653 : exactInterval 15 2653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2653 : oddCount 2653 15 = 5 ∧ acceleratedOrbit 15 2653 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2653) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2653.1, data_15_2653.2]

end Collatz.Research.PassageAtlas.Batch0081
