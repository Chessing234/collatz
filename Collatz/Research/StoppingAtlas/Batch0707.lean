import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0707

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3676. -/
theorem bounds_13_3676 : exactInterval 13 3676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3676 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3676) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3676 : oddCount 3676 13 = 5 ∧ acceleratedOrbit 13 3676 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3676 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3676) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3676.1, data_13_3676.2]

/-- Complete interval computation for depth 13, residue 3677. -/
theorem bounds_13_3677 : exactInterval 13 3677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3677 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3677) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3677 : oddCount 3677 13 = 5 ∧ acceleratedOrbit 13 3677 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3677 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3677) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3677.1, data_13_3677.2]

/-- Complete interval computation for depth 13, residue 3678. -/
theorem bounds_13_3678 : exactInterval 13 3678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3678 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3678) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3678 : oddCount 3678 13 = 7 ∧ acceleratedOrbit 13 3678 = 983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3678 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3678) = 3 ^ 7 * m + 983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3678.1, data_13_3678.2]

/-- Complete interval computation for depth 13, residue 3679. -/
theorem bounds_13_3679 : exactInterval 13 3679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3679 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3679) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3679 : oddCount 3679 13 = 7 ∧ acceleratedOrbit 13 3679 = 983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3679 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3679) = 3 ^ 7 * m + 983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3679.1, data_13_3679.2]

/-- Complete interval computation for depth 13, residue 3680. -/
theorem bounds_13_3680 : exactInterval 13 3680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3680 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3680) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3680 : oddCount 3680 13 = 4 ∧ acceleratedOrbit 13 3680 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3680 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3680) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3680.1, data_13_3680.2]

/-- Complete interval computation for depth 13, residue 3681. -/
theorem bounds_13_3681 : exactInterval 13 3681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3681 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3681) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3681 : oddCount 3681 13 = 6 ∧ acceleratedOrbit 13 3681 = 328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3681 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3681) = 3 ^ 6 * m + 328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3681.1, data_13_3681.2]

/-- Complete interval computation for depth 13, residue 3682. -/
theorem bounds_13_3682 : exactInterval 13 3682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3682 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3682) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3682 : oddCount 3682 13 = 5 ∧ acceleratedOrbit 13 3682 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3682 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3682) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3682.1, data_13_3682.2]

/-- Complete interval computation for depth 13, residue 3683. -/
theorem bounds_13_3683 : exactInterval 13 3683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3683 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3683) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3683 : oddCount 3683 13 = 5 ∧ acceleratedOrbit 13 3683 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3683 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3683) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3683.1, data_13_3683.2]

/-- Complete interval computation for depth 13, residue 3684. -/
theorem bounds_13_3684 : exactInterval 13 3684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3684 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3684) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3684 : oddCount 3684 13 = 5 ∧ acceleratedOrbit 13 3684 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3684 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3684) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3684.1, data_13_3684.2]

/-- Complete interval computation for depth 13, residue 3685. -/
theorem bounds_13_3685 : exactInterval 13 3685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3685 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3685) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3685 : oddCount 3685 13 = 5 ∧ acceleratedOrbit 13 3685 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3685 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3685) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3685.1, data_13_3685.2]

/-- Complete interval computation for depth 13, residue 3686. -/
theorem bounds_13_3686 : exactInterval 13 3686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3686 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3686) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3686 : oddCount 3686 13 = 5 ∧ acceleratedOrbit 13 3686 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3686 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3686) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3686.1, data_13_3686.2]

/-- Complete interval computation for depth 13, residue 3687. -/
theorem bounds_13_3687 : exactInterval 13 3687 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3687 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3687) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3687 : oddCount 3687 13 = 8 ∧ acceleratedOrbit 13 3687 = 2954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3687 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3687) = 3 ^ 8 * m + 2954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3687.1, data_13_3687.2]

/-- Complete interval computation for depth 13, residue 3688. -/
theorem bounds_13_3688 : exactInterval 13 3688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3688 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3688) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3688 : oddCount 3688 13 = 4 ∧ acceleratedOrbit 13 3688 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3688 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3688) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3688.1, data_13_3688.2]

/-- Complete interval computation for depth 13, residue 3689. -/
theorem bounds_13_3689 : exactInterval 13 3689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3689 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3689) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3689 : oddCount 3689 13 = 9 ∧ acceleratedOrbit 13 3689 = 8869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3689 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3689) = 3 ^ 9 * m + 8869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3689.1, data_13_3689.2]

/-- Complete interval computation for depth 13, residue 3690. -/
theorem bounds_13_3690 : exactInterval 13 3690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3690 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3690) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3690 : oddCount 3690 13 = 4 ∧ acceleratedOrbit 13 3690 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3690 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3690) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3690.1, data_13_3690.2]

end Collatz.Research.StoppingAtlas.Batch0707
