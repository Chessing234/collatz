import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0642

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2677. -/
theorem bounds_13_2677 : exactInterval 13 2677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2677 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2677) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2677 : oddCount 2677 13 = 7 ∧ acceleratedOrbit 13 2677 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2677 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2677) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2677.1, data_13_2677.2]

/-- Complete interval computation for depth 13, residue 2678. -/
theorem bounds_13_2678 : exactInterval 13 2678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2678 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2678) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2678 : oddCount 2678 13 = 5 ∧ acceleratedOrbit 13 2678 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2678 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2678) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2678.1, data_13_2678.2]

/-- Complete interval computation for depth 13, residue 2679. -/
theorem bounds_13_2679 : exactInterval 13 2679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2679 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2679) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2679 : oddCount 2679 13 = 5 ∧ acceleratedOrbit 13 2679 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2679 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2679) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2679.1, data_13_2679.2]

/-- Complete interval computation for depth 13, residue 2680. -/
theorem bounds_13_2680 : exactInterval 13 2680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2680 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2680) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2680 : oddCount 2680 13 = 7 ∧ acceleratedOrbit 13 2680 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2680 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2680) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2680.1, data_13_2680.2]

/-- Complete interval computation for depth 13, residue 2681. -/
theorem bounds_13_2681 : exactInterval 13 2681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2681 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2681) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2681 : oddCount 2681 13 = 8 ∧ acceleratedOrbit 13 2681 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2681 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2681) = 3 ^ 8 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2681.1, data_13_2681.2]

/-- Complete interval computation for depth 13, residue 2682. -/
theorem bounds_13_2682 : exactInterval 13 2682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2682 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2682) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2682 : oddCount 2682 13 = 7 ∧ acceleratedOrbit 13 2682 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2682 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2682) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2682.1, data_13_2682.2]

/-- Complete interval computation for depth 13, residue 2683. -/
theorem bounds_13_2683 : exactInterval 13 2683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2683 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2683) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2683 : oddCount 2683 13 = 6 ∧ acceleratedOrbit 13 2683 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2683 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2683) = 3 ^ 6 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2683.1, data_13_2683.2]

/-- Complete interval computation for depth 13, residue 2684. -/
theorem bounds_13_2684 : exactInterval 13 2684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2684 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2684) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2684 : oddCount 2684 13 = 8 ∧ acceleratedOrbit 13 2684 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2684 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2684) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2684.1, data_13_2684.2]

/-- Complete interval computation for depth 13, residue 2685. -/
theorem bounds_13_2685 : exactInterval 13 2685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2685 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2685) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2685 : oddCount 2685 13 = 8 ∧ acceleratedOrbit 13 2685 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2685 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2685) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2685.1, data_13_2685.2]

/-- Complete interval computation for depth 13, residue 2686. -/
theorem bounds_13_2686 : exactInterval 13 2686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2686 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2686) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2686 : oddCount 2686 13 = 8 ∧ acceleratedOrbit 13 2686 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2686 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2686) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2686.1, data_13_2686.2]

/-- Complete interval computation for depth 13, residue 2687. -/
theorem bounds_13_2687 : exactInterval 13 2687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2687 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2687) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2687 : oddCount 2687 13 = 10 ∧ acceleratedOrbit 13 2687 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2687 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2687) = 3 ^ 10 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2687.1, data_13_2687.2]

/-- Complete interval computation for depth 13, residue 2688. -/
theorem bounds_13_2688 : exactInterval 13 2688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2688 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2688) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2688 : oddCount 2688 13 = 1 ∧ acceleratedOrbit 13 2688 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2688 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2688) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2688.1, data_13_2688.2]

/-- Complete interval computation for depth 13, residue 2689. -/
theorem bounds_13_2689 : exactInterval 13 2689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2689 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2689) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2689 : oddCount 2689 13 = 9 ∧ acceleratedOrbit 13 2689 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2689 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2689) = 3 ^ 9 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2689.1, data_13_2689.2]

/-- Complete interval computation for depth 13, residue 2690. -/
theorem bounds_13_2690 : exactInterval 13 2690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2690 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2690) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2690 : oddCount 2690 13 = 6 ∧ acceleratedOrbit 13 2690 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2690 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2690) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2690.1, data_13_2690.2]

/-- Complete interval computation for depth 13, residue 2691. -/
theorem bounds_13_2691 : exactInterval 13 2691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2691 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2691) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2691 : oddCount 2691 13 = 6 ∧ acceleratedOrbit 13 2691 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2691 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2691) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2691.1, data_13_2691.2]

/-- Complete interval computation for depth 13, residue 2692. -/
theorem bounds_13_2692 : exactInterval 13 2692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2692 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2692) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2692 : oddCount 2692 13 = 7 ∧ acceleratedOrbit 13 2692 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2692 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2692) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2692.1, data_13_2692.2]

end Collatz.Research.StoppingAtlas.Batch0642
