import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0082

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2654. -/
theorem bounds_15_2654 : exactInterval 15 2654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2654 : oddCount 2654 15 = 8 ∧ acceleratedOrbit 15 2654 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2654) = 3 ^ 8 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2654.1, data_15_2654.2]

/-- Complete interval computation for depth 15, residue 2655. -/
theorem bounds_15_2655 : exactInterval 15 2655 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2655 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2655) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2655 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2655 : oddCount 2655 15 = 8 ∧ acceleratedOrbit 15 2655 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2655 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2655) = 3 ^ 8 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2655.1, data_15_2655.2]

/-- Complete interval computation for depth 15, residue 2656. -/
theorem bounds_15_2656 : exactInterval 15 2656 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2656 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2656) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2656 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2656 : oddCount 2656 15 = 7 ∧ acceleratedOrbit 15 2656 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2656 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2656) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2656.1, data_15_2656.2]

/-- Complete interval computation for depth 15, residue 2657. -/
theorem bounds_15_2657 : exactInterval 15 2657 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2657 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2657) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2657 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2657 : oddCount 2657 15 = 8 ∧ acceleratedOrbit 15 2657 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2657 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2657) = 3 ^ 8 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2657.1, data_15_2657.2]

/-- Complete interval computation for depth 15, residue 2658. -/
theorem bounds_15_2658 : exactInterval 15 2658 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2658 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2658) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2658 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2658 : oddCount 2658 15 = 7 ∧ acceleratedOrbit 15 2658 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2658 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2658) = 3 ^ 7 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2658.1, data_15_2658.2]

/-- Complete interval computation for depth 15, residue 2659. -/
theorem bounds_15_2659 : exactInterval 15 2659 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2659 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2659) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2659 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2659 : oddCount 2659 15 = 7 ∧ acceleratedOrbit 15 2659 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2659 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2659) = 3 ^ 7 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2659.1, data_15_2659.2]

/-- Complete interval computation for depth 15, residue 2660. -/
theorem bounds_15_2660 : exactInterval 15 2660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2660 : oddCount 2660 15 = 7 ∧ acceleratedOrbit 15 2660 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2660) = 3 ^ 7 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2660.1, data_15_2660.2]

/-- Complete interval computation for depth 15, residue 2661. -/
theorem bounds_15_2661 : exactInterval 15 2661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2661 : oddCount 2661 15 = 7 ∧ acceleratedOrbit 15 2661 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2661) = 3 ^ 7 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2661.1, data_15_2661.2]

/-- Complete interval computation for depth 15, residue 2662. -/
theorem bounds_15_2662 : exactInterval 15 2662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2662 : oddCount 2662 15 = 7 ∧ acceleratedOrbit 15 2662 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2662) = 3 ^ 7 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2662.1, data_15_2662.2]

/-- Complete interval computation for depth 15, residue 2663. -/
theorem bounds_15_2663 : exactInterval 15 2663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2663 : oddCount 2663 15 = 9 ∧ acceleratedOrbit 15 2663 = 1601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2663) = 3 ^ 9 * m + 1601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2663.1, data_15_2663.2]

/-- Complete interval computation for depth 15, residue 2664. -/
theorem bounds_15_2664 : exactInterval 15 2664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2664 : oddCount 2664 15 = 7 ∧ acceleratedOrbit 15 2664 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2664) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2664.1, data_15_2664.2]

/-- Complete interval computation for depth 15, residue 2665. -/
theorem bounds_15_2665 : exactInterval 15 2665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2665 : oddCount 2665 15 = 7 ∧ acceleratedOrbit 15 2665 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2665) = 3 ^ 7 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2665.1, data_15_2665.2]

/-- Complete interval computation for depth 15, residue 2666. -/
theorem bounds_15_2666 : exactInterval 15 2666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2666 : oddCount 2666 15 = 7 ∧ acceleratedOrbit 15 2666 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2666) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2666.1, data_15_2666.2]

/-- Complete interval computation for depth 15, residue 2667. -/
theorem bounds_15_2667 : exactInterval 15 2667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2667 : oddCount 2667 15 = 8 ∧ acceleratedOrbit 15 2667 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2667) = 3 ^ 8 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2667.1, data_15_2667.2]

/-- Complete interval computation for depth 15, residue 2668. -/
theorem bounds_15_2668 : exactInterval 15 2668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2668 : oddCount 2668 15 = 10 ∧ acceleratedOrbit 15 2668 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2668) = 3 ^ 10 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2668.1, data_15_2668.2]

/-- Complete interval computation for depth 15, residue 2669. -/
theorem bounds_15_2669 : exactInterval 15 2669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2669 : oddCount 2669 15 = 10 ∧ acceleratedOrbit 15 2669 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2669) = 3 ^ 10 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2669.1, data_15_2669.2]

/-- Complete interval computation for depth 15, residue 2670. -/
theorem bounds_15_2670 : exactInterval 15 2670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2670 : oddCount 2670 15 = 10 ∧ acceleratedOrbit 15 2670 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2670) = 3 ^ 10 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2670.1, data_15_2670.2]

/-- Complete interval computation for depth 15, residue 2671. -/
theorem bounds_15_2671 : exactInterval 15 2671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2671 : oddCount 2671 15 = 10 ∧ acceleratedOrbit 15 2671 = 4816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2671) = 3 ^ 10 * m + 4816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2671.1, data_15_2671.2]

/-- Complete interval computation for depth 15, residue 2672. -/
theorem bounds_15_2672 : exactInterval 15 2672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2672 : oddCount 2672 15 = 9 ∧ acceleratedOrbit 15 2672 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2672) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2672.1, data_15_2672.2]

/-- Complete interval computation for depth 15, residue 2673. -/
theorem bounds_15_2673 : exactInterval 15 2673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2673 : oddCount 2673 15 = 7 ∧ acceleratedOrbit 15 2673 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2673) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2673.1, data_15_2673.2]

/-- Complete interval computation for depth 15, residue 2674. -/
theorem bounds_15_2674 : exactInterval 15 2674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2674 : oddCount 2674 15 = 9 ∧ acceleratedOrbit 15 2674 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2674) = 3 ^ 9 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2674.1, data_15_2674.2]

/-- Complete interval computation for depth 15, residue 2675. -/
theorem bounds_15_2675 : exactInterval 15 2675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2675 : oddCount 2675 15 = 9 ∧ acceleratedOrbit 15 2675 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2675) = 3 ^ 9 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2675.1, data_15_2675.2]

/-- Complete interval computation for depth 15, residue 2676. -/
theorem bounds_15_2676 : exactInterval 15 2676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2676 : oddCount 2676 15 = 9 ∧ acceleratedOrbit 15 2676 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2676) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2676.1, data_15_2676.2]

/-- Complete interval computation for depth 15, residue 2677. -/
theorem bounds_15_2677 : exactInterval 15 2677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2677 : oddCount 2677 15 = 9 ∧ acceleratedOrbit 15 2677 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2677) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2677.1, data_15_2677.2]

/-- Complete interval computation for depth 15, residue 2678. -/
theorem bounds_15_2678 : exactInterval 15 2678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2678 : oddCount 2678 15 = 5 ∧ acceleratedOrbit 15 2678 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2678) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2678.1, data_15_2678.2]

/-- Complete interval computation for depth 15, residue 2679. -/
theorem bounds_15_2679 : exactInterval 15 2679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2679 : oddCount 2679 15 = 5 ∧ acceleratedOrbit 15 2679 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2679) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2679.1, data_15_2679.2]

/-- Complete interval computation for depth 15, residue 2680. -/
theorem bounds_15_2680 : exactInterval 15 2680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2680 : oddCount 2680 15 = 9 ∧ acceleratedOrbit 15 2680 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2680) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2680.1, data_15_2680.2]

/-- Complete interval computation for depth 15, residue 2681. -/
theorem bounds_15_2681 : exactInterval 15 2681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2681 : oddCount 2681 15 = 9 ∧ acceleratedOrbit 15 2681 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2681) = 3 ^ 9 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2681.1, data_15_2681.2]

/-- Complete interval computation for depth 15, residue 2682. -/
theorem bounds_15_2682 : exactInterval 15 2682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2682 : oddCount 2682 15 = 9 ∧ acceleratedOrbit 15 2682 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2682) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2682.1, data_15_2682.2]

/-- Complete interval computation for depth 15, residue 2683. -/
theorem bounds_15_2683 : exactInterval 15 2683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2683 : oddCount 2683 15 = 8 ∧ acceleratedOrbit 15 2683 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2683) = 3 ^ 8 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2683.1, data_15_2683.2]

/-- Complete interval computation for depth 15, residue 2684. -/
theorem bounds_15_2684 : exactInterval 15 2684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2684 : oddCount 2684 15 = 9 ∧ acceleratedOrbit 15 2684 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2684) = 3 ^ 9 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2684.1, data_15_2684.2]

/-- Complete interval computation for depth 15, residue 2685. -/
theorem bounds_15_2685 : exactInterval 15 2685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2685 : oddCount 2685 15 = 9 ∧ acceleratedOrbit 15 2685 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2685) = 3 ^ 9 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2685.1, data_15_2685.2]

end Collatz.Research.PassageAtlas.Batch0082
