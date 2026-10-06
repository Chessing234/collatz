import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0643

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2693. -/
theorem bounds_13_2693 : exactInterval 13 2693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2693 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2693) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2693 : oddCount 2693 13 = 7 ∧ acceleratedOrbit 13 2693 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2693 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2693) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2693.1, data_13_2693.2]

/-- Complete interval computation for depth 13, residue 2694. -/
theorem bounds_13_2694 : exactInterval 13 2694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2694 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2694) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2694 : oddCount 2694 13 = 7 ∧ acceleratedOrbit 13 2694 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2694 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2694) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2694.1, data_13_2694.2]

/-- Complete interval computation for depth 13, residue 2695. -/
theorem bounds_13_2695 : exactInterval 13 2695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2695 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2695) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2695 : oddCount 2695 13 = 5 ∧ acceleratedOrbit 13 2695 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2695 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2695) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2695.1, data_13_2695.2]

/-- Complete interval computation for depth 13, residue 2696. -/
theorem bounds_13_2696 : exactInterval 13 2696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2696 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2696) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2696 : oddCount 2696 13 = 7 ∧ acceleratedOrbit 13 2696 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2696 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2696) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2696.1, data_13_2696.2]

/-- Complete interval computation for depth 13, residue 2697. -/
theorem bounds_13_2697 : exactInterval 13 2697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2697 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2697) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2697 : oddCount 2697 13 = 8 ∧ acceleratedOrbit 13 2697 = 2162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2697 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2697) = 3 ^ 8 * m + 2162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2697.1, data_13_2697.2]

/-- Complete interval computation for depth 13, residue 2698. -/
theorem bounds_13_2698 : exactInterval 13 2698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2698 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2698) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2698 : oddCount 2698 13 = 7 ∧ acceleratedOrbit 13 2698 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2698 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2698) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2698.1, data_13_2698.2]

/-- Complete interval computation for depth 13, residue 2699. -/
theorem bounds_13_2699 : exactInterval 13 2699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2699 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2699) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2699 : oddCount 2699 13 = 7 ∧ acceleratedOrbit 13 2699 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2699 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2699) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2699.1, data_13_2699.2]

/-- Complete interval computation for depth 13, residue 2700. -/
theorem bounds_13_2700 : exactInterval 13 2700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2700 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2700) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2700 : oddCount 2700 13 = 7 ∧ acceleratedOrbit 13 2700 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2700 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2700) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2700.1, data_13_2700.2]

/-- Complete interval computation for depth 13, residue 2701. -/
theorem bounds_13_2701 : exactInterval 13 2701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2701 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2701) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2701 : oddCount 2701 13 = 7 ∧ acceleratedOrbit 13 2701 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2701 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2701) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2701.1, data_13_2701.2]

/-- Complete interval computation for depth 13, residue 2702. -/
theorem bounds_13_2702 : exactInterval 13 2702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2702 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2702) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2702 : oddCount 2702 13 = 9 ∧ acceleratedOrbit 13 2702 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2702 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2702) = 3 ^ 9 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2702.1, data_13_2702.2]

/-- Complete interval computation for depth 13, residue 2703. -/
theorem bounds_13_2703 : exactInterval 13 2703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2703 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2703) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2703 : oddCount 2703 13 = 9 ∧ acceleratedOrbit 13 2703 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2703 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2703) = 3 ^ 9 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2703.1, data_13_2703.2]

/-- Complete interval computation for depth 13, residue 2704. -/
theorem bounds_13_2704 : exactInterval 13 2704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2704 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2704) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2704 : oddCount 2704 13 = 8 ∧ acceleratedOrbit 13 2704 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2704 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2704) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2704.1, data_13_2704.2]

/-- Complete interval computation for depth 13, residue 2705. -/
theorem bounds_13_2705 : exactInterval 13 2705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2705 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2705) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2705 : oddCount 2705 13 = 7 ∧ acceleratedOrbit 13 2705 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2705 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2705) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2705.1, data_13_2705.2]

/-- Complete interval computation for depth 13, residue 2706. -/
theorem bounds_13_2706 : exactInterval 13 2706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2706 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2706) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2706 : oddCount 2706 13 = 7 ∧ acceleratedOrbit 13 2706 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2706 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2706) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2706.1, data_13_2706.2]

/-- Complete interval computation for depth 13, residue 2707. -/
theorem bounds_13_2707 : exactInterval 13 2707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2707 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2707) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2707 : oddCount 2707 13 = 7 ∧ acceleratedOrbit 13 2707 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2707 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2707) = 3 ^ 7 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2707.1, data_13_2707.2]

end Collatz.Research.StoppingAtlas.Batch0643
