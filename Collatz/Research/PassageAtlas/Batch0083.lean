import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0083

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2686. -/
theorem bounds_15_2686 : exactInterval 15 2686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2686 : oddCount 2686 15 = 9 ∧ acceleratedOrbit 15 2686 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2686) = 3 ^ 9 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2686.1, data_15_2686.2]

/-- Complete interval computation for depth 15, residue 2687. -/
theorem bounds_15_2687 : exactInterval 15 2687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2687 : oddCount 2687 15 = 10 ∧ acceleratedOrbit 15 2687 = 4844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2687) = 3 ^ 10 * m + 4844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2687.1, data_15_2687.2]

/-- Complete interval computation for depth 15, residue 2688. -/
theorem bounds_15_2688 : exactInterval 15 2688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2688 : oddCount 2688 15 = 2 ∧ acceleratedOrbit 15 2688 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2688) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2688.1, data_15_2688.2]

/-- Complete interval computation for depth 15, residue 2689. -/
theorem bounds_15_2689 : exactInterval 15 2689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2689 : oddCount 2689 15 = 10 ∧ acceleratedOrbit 15 2689 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2689) = 3 ^ 10 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2689.1, data_15_2689.2]

/-- Complete interval computation for depth 15, residue 2690. -/
theorem bounds_15_2690 : exactInterval 15 2690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2690 : oddCount 2690 15 = 7 ∧ acceleratedOrbit 15 2690 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2690) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2690.1, data_15_2690.2]

/-- Complete interval computation for depth 15, residue 2691. -/
theorem bounds_15_2691 : exactInterval 15 2691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2691 : oddCount 2691 15 = 7 ∧ acceleratedOrbit 15 2691 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2691) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2691.1, data_15_2691.2]

/-- Complete interval computation for depth 15, residue 2692. -/
theorem bounds_15_2692 : exactInterval 15 2692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2692 : oddCount 2692 15 = 8 ∧ acceleratedOrbit 15 2692 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2692) = 3 ^ 8 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2692.1, data_15_2692.2]

/-- Complete interval computation for depth 15, residue 2693. -/
theorem bounds_15_2693 : exactInterval 15 2693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2693 : oddCount 2693 15 = 8 ∧ acceleratedOrbit 15 2693 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2693) = 3 ^ 8 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2693.1, data_15_2693.2]

/-- Complete interval computation for depth 15, residue 2694. -/
theorem bounds_15_2694 : exactInterval 15 2694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2694 : oddCount 2694 15 = 8 ∧ acceleratedOrbit 15 2694 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2694) = 3 ^ 8 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2694.1, data_15_2694.2]

/-- Complete interval computation for depth 15, residue 2695. -/
theorem bounds_15_2695 : exactInterval 15 2695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2695 : oddCount 2695 15 = 5 ∧ acceleratedOrbit 15 2695 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2695) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2695.1, data_15_2695.2]

/-- Complete interval computation for depth 15, residue 2696. -/
theorem bounds_15_2696 : exactInterval 15 2696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2696 : oddCount 2696 15 = 7 ∧ acceleratedOrbit 15 2696 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2696) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2696.1, data_15_2696.2]

/-- Complete interval computation for depth 15, residue 2697. -/
theorem bounds_15_2697 : exactInterval 15 2697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2697 : oddCount 2697 15 = 9 ∧ acceleratedOrbit 15 2697 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2697) = 3 ^ 9 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2697.1, data_15_2697.2]

/-- Complete interval computation for depth 15, residue 2698. -/
theorem bounds_15_2698 : exactInterval 15 2698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2698 : oddCount 2698 15 = 7 ∧ acceleratedOrbit 15 2698 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2698) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2698.1, data_15_2698.2]

/-- Complete interval computation for depth 15, residue 2699. -/
theorem bounds_15_2699 : exactInterval 15 2699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2699 : oddCount 2699 15 = 8 ∧ acceleratedOrbit 15 2699 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2699) = 3 ^ 8 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2699.1, data_15_2699.2]

/-- Complete interval computation for depth 15, residue 2700. -/
theorem bounds_15_2700 : exactInterval 15 2700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2700 : oddCount 2700 15 = 7 ∧ acceleratedOrbit 15 2700 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2700) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2700.1, data_15_2700.2]

/-- Complete interval computation for depth 15, residue 2701. -/
theorem bounds_15_2701 : exactInterval 15 2701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2701 : oddCount 2701 15 = 7 ∧ acceleratedOrbit 15 2701 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2701) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2701.1, data_15_2701.2]

/-- Complete interval computation for depth 15, residue 2702. -/
theorem bounds_15_2702 : exactInterval 15 2702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2702 : oddCount 2702 15 = 9 ∧ acceleratedOrbit 15 2702 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2702) = 3 ^ 9 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2702.1, data_15_2702.2]

/-- Complete interval computation for depth 15, residue 2703. -/
theorem bounds_15_2703 : exactInterval 15 2703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2703 : oddCount 2703 15 = 9 ∧ acceleratedOrbit 15 2703 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2703) = 3 ^ 9 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2703.1, data_15_2703.2]

/-- Complete interval computation for depth 15, residue 2704. -/
theorem bounds_15_2704 : exactInterval 15 2704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2704 : oddCount 2704 15 = 9 ∧ acceleratedOrbit 15 2704 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2704) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2704.1, data_15_2704.2]

/-- Complete interval computation for depth 15, residue 2705. -/
theorem bounds_15_2705 : exactInterval 15 2705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2705 : oddCount 2705 15 = 7 ∧ acceleratedOrbit 15 2705 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2705) = 3 ^ 7 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2705.1, data_15_2705.2]

/-- Complete interval computation for depth 15, residue 2706. -/
theorem bounds_15_2706 : exactInterval 15 2706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2706 : oddCount 2706 15 = 7 ∧ acceleratedOrbit 15 2706 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2706) = 3 ^ 7 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2706.1, data_15_2706.2]

/-- Complete interval computation for depth 15, residue 2707. -/
theorem bounds_15_2707 : exactInterval 15 2707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2707 : oddCount 2707 15 = 7 ∧ acceleratedOrbit 15 2707 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2707) = 3 ^ 7 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2707.1, data_15_2707.2]

/-- Complete interval computation for depth 15, residue 2708. -/
theorem bounds_15_2708 : exactInterval 15 2708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2708 : oddCount 2708 15 = 9 ∧ acceleratedOrbit 15 2708 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2708) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2708.1, data_15_2708.2]

/-- Complete interval computation for depth 15, residue 2709. -/
theorem bounds_15_2709 : exactInterval 15 2709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2709 : oddCount 2709 15 = 9 ∧ acceleratedOrbit 15 2709 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2709) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2709.1, data_15_2709.2]

/-- Complete interval computation for depth 15, residue 2710. -/
theorem bounds_15_2710 : exactInterval 15 2710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2710 : oddCount 2710 15 = 7 ∧ acceleratedOrbit 15 2710 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2710) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2710.1, data_15_2710.2]

/-- Complete interval computation for depth 15, residue 2711. -/
theorem bounds_15_2711 : exactInterval 15 2711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2711 : oddCount 2711 15 = 7 ∧ acceleratedOrbit 15 2711 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2711) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2711.1, data_15_2711.2]

/-- Complete interval computation for depth 15, residue 2712. -/
theorem bounds_15_2712 : exactInterval 15 2712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2712 : oddCount 2712 15 = 9 ∧ acceleratedOrbit 15 2712 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2712) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2712.1, data_15_2712.2]

/-- Complete interval computation for depth 15, residue 2713. -/
theorem bounds_15_2713 : exactInterval 15 2713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2713 : oddCount 2713 15 = 9 ∧ acceleratedOrbit 15 2713 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2713) = 3 ^ 9 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2713.1, data_15_2713.2]

/-- Complete interval computation for depth 15, residue 2714. -/
theorem bounds_15_2714 : exactInterval 15 2714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2714 : oddCount 2714 15 = 9 ∧ acceleratedOrbit 15 2714 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2714) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2714.1, data_15_2714.2]

/-- Complete interval computation for depth 15, residue 2715. -/
theorem bounds_15_2715 : exactInterval 15 2715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2715 : oddCount 2715 15 = 11 ∧ acceleratedOrbit 15 2715 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2715) = 3 ^ 11 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2715.1, data_15_2715.2]

/-- Complete interval computation for depth 15, residue 2716. -/
theorem bounds_15_2716 : exactInterval 15 2716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2716 : oddCount 2716 15 = 8 ∧ acceleratedOrbit 15 2716 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2716) = 3 ^ 8 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2716.1, data_15_2716.2]

/-- Complete interval computation for depth 15, residue 2717. -/
theorem bounds_15_2717 : exactInterval 15 2717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2717 : oddCount 2717 15 = 8 ∧ acceleratedOrbit 15 2717 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2717) = 3 ^ 8 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2717.1, data_15_2717.2]

/-- Complete interval computation for depth 15, residue 2718. -/
theorem bounds_15_2718 : exactInterval 15 2718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2718 : oddCount 2718 15 = 8 ∧ acceleratedOrbit 15 2718 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2718) = 3 ^ 8 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2718.1, data_15_2718.2]

end Collatz.Research.PassageAtlas.Batch0083
