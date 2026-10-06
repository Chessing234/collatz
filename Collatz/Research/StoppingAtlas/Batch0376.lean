import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0376

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2688. -/
theorem bounds_12_2688 : exactInterval 12 2688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2688 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2688) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2688 : oddCount 2688 12 = 1 ∧ acceleratedOrbit 12 2688 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2688 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2688) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2688.1, data_12_2688.2]

/-- Complete interval computation for depth 12, residue 2689. -/
theorem bounds_12_2689 : exactInterval 12 2689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2689 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2689) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2689 : oddCount 2689 12 = 8 ∧ acceleratedOrbit 12 2689 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2689 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2689) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2689.1, data_12_2689.2]

/-- Complete interval computation for depth 12, residue 2690. -/
theorem bounds_12_2690 : exactInterval 12 2690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2690 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2690) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2690 : oddCount 2690 12 = 5 ∧ acceleratedOrbit 12 2690 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2690 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2690) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2690.1, data_12_2690.2]

/-- Complete interval computation for depth 12, residue 2691. -/
theorem bounds_12_2691 : exactInterval 12 2691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2691 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2691) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2691 : oddCount 2691 12 = 5 ∧ acceleratedOrbit 12 2691 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2691 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2691) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2691.1, data_12_2691.2]

/-- Complete interval computation for depth 12, residue 2692. -/
theorem bounds_12_2692 : exactInterval 12 2692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2692 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2692) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2692 : oddCount 2692 12 = 6 ∧ acceleratedOrbit 12 2692 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2692 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2692) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2692.1, data_12_2692.2]

/-- Complete interval computation for depth 12, residue 2693. -/
theorem bounds_12_2693 : exactInterval 12 2693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2693 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2693) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2693 : oddCount 2693 12 = 6 ∧ acceleratedOrbit 12 2693 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2693 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2693) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2693.1, data_12_2693.2]

/-- Complete interval computation for depth 12, residue 2694. -/
theorem bounds_12_2694 : exactInterval 12 2694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2694 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2694) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2694 : oddCount 2694 12 = 6 ∧ acceleratedOrbit 12 2694 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2694 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2694) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2694.1, data_12_2694.2]

/-- Complete interval computation for depth 12, residue 2695. -/
theorem bounds_12_2695 : exactInterval 12 2695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2695 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2695) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2695 : oddCount 2695 12 = 5 ∧ acceleratedOrbit 12 2695 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2695 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2695) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2695.1, data_12_2695.2]

/-- Complete interval computation for depth 12, residue 2696. -/
theorem bounds_12_2696 : exactInterval 12 2696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2696 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2696) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2696 : oddCount 2696 12 = 6 ∧ acceleratedOrbit 12 2696 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2696 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2696) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2696.1, data_12_2696.2]

/-- Complete interval computation for depth 12, residue 2697. -/
theorem bounds_12_2697 : exactInterval 12 2697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2697 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2697) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2697 : oddCount 2697 12 = 7 ∧ acceleratedOrbit 12 2697 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2697 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2697) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2697.1, data_12_2697.2]

/-- Complete interval computation for depth 12, residue 2698. -/
theorem bounds_12_2698 : exactInterval 12 2698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2698 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2698) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2698 : oddCount 2698 12 = 6 ∧ acceleratedOrbit 12 2698 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2698 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2698) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2698.1, data_12_2698.2]

/-- Complete interval computation for depth 12, residue 2699. -/
theorem bounds_12_2699 : exactInterval 12 2699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2699 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2699) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2699 : oddCount 2699 12 = 6 ∧ acceleratedOrbit 12 2699 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2699 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2699) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2699.1, data_12_2699.2]

/-- Complete interval computation for depth 12, residue 2700. -/
theorem bounds_12_2700 : exactInterval 12 2700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2700 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2700) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2700 : oddCount 2700 12 = 6 ∧ acceleratedOrbit 12 2700 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2700 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2700) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2700.1, data_12_2700.2]

/-- Complete interval computation for depth 12, residue 2701. -/
theorem bounds_12_2701 : exactInterval 12 2701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2701 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2701) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2701 : oddCount 2701 12 = 6 ∧ acceleratedOrbit 12 2701 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2701 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2701) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2701.1, data_12_2701.2]

/-- Complete interval computation for depth 12, residue 2702. -/
theorem bounds_12_2702 : exactInterval 12 2702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2702 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2702) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2702 : oddCount 2702 12 = 8 ∧ acceleratedOrbit 12 2702 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2702 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2702) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2702.1, data_12_2702.2]

end Collatz.Research.StoppingAtlas.Batch0376
