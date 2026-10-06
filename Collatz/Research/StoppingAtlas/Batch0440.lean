import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0440

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3671. -/
theorem bounds_12_3671 : exactInterval 12 3671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3671 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3671) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3671 : oddCount 3671 12 = 5 ∧ acceleratedOrbit 12 3671 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3671 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3671) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3671.1, data_12_3671.2]

/-- Complete interval computation for depth 12, residue 3672. -/
theorem bounds_12_3672 : exactInterval 12 3672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3672 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3672) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3672 : oddCount 3672 12 = 4 ∧ acceleratedOrbit 12 3672 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3672 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3672) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3672.1, data_12_3672.2]

/-- Complete interval computation for depth 12, residue 3673. -/
theorem bounds_12_3673 : exactInterval 12 3673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3673 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3673) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3673 : oddCount 3673 12 = 7 ∧ acceleratedOrbit 12 3673 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3673 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3673) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3673.1, data_12_3673.2]

/-- Complete interval computation for depth 12, residue 3674. -/
theorem bounds_12_3674 : exactInterval 12 3674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3674 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3674) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3674 : oddCount 3674 12 = 4 ∧ acceleratedOrbit 12 3674 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3674 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3674) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3674.1, data_12_3674.2]

/-- Complete interval computation for depth 12, residue 3675. -/
theorem bounds_12_3675 : exactInterval 12 3675 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3675 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3675) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3675 : oddCount 3675 12 = 7 ∧ acceleratedOrbit 12 3675 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3675 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3675) = 3 ^ 7 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3675.1, data_12_3675.2]

/-- Complete interval computation for depth 12, residue 3676. -/
theorem bounds_12_3676 : exactInterval 12 3676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3676 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3676) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3676 : oddCount 3676 12 = 4 ∧ acceleratedOrbit 12 3676 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3676 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3676) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3676.1, data_12_3676.2]

/-- Complete interval computation for depth 12, residue 3677. -/
theorem bounds_12_3677 : exactInterval 12 3677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3677 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3677) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3677 : oddCount 3677 12 = 4 ∧ acceleratedOrbit 12 3677 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3677 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3677) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3677.1, data_12_3677.2]

/-- Complete interval computation for depth 12, residue 3678. -/
theorem bounds_12_3678 : exactInterval 12 3678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3678 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3678) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3678 : oddCount 3678 12 = 6 ∧ acceleratedOrbit 12 3678 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3678 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3678) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3678.1, data_12_3678.2]

/-- Complete interval computation for depth 12, residue 3679. -/
theorem bounds_12_3679 : exactInterval 12 3679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3679 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3679) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3679 : oddCount 3679 12 = 6 ∧ acceleratedOrbit 12 3679 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3679 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3679) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3679.1, data_12_3679.2]

/-- Complete interval computation for depth 12, residue 3680. -/
theorem bounds_12_3680 : exactInterval 12 3680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3680 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3680) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3680 : oddCount 3680 12 = 4 ∧ acceleratedOrbit 12 3680 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3680 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3680) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3680.1, data_12_3680.2]

/-- Complete interval computation for depth 12, residue 3681. -/
theorem bounds_12_3681 : exactInterval 12 3681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3681 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3681) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3681 : oddCount 3681 12 = 6 ∧ acceleratedOrbit 12 3681 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3681 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3681) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3681.1, data_12_3681.2]

/-- Complete interval computation for depth 12, residue 3682. -/
theorem bounds_12_3682 : exactInterval 12 3682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3682 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3682) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3682 : oddCount 3682 12 = 4 ∧ acceleratedOrbit 12 3682 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3682 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3682) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3682.1, data_12_3682.2]

/-- Complete interval computation for depth 12, residue 3683. -/
theorem bounds_12_3683 : exactInterval 12 3683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3683 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3683) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3683 : oddCount 3683 12 = 4 ∧ acceleratedOrbit 12 3683 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3683 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3683) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3683.1, data_12_3683.2]

/-- Complete interval computation for depth 12, residue 3684. -/
theorem bounds_12_3684 : exactInterval 12 3684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3684 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3684) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3684 : oddCount 3684 12 = 4 ∧ acceleratedOrbit 12 3684 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3684 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3684) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3684.1, data_12_3684.2]

/-- Complete interval computation for depth 12, residue 3685. -/
theorem bounds_12_3685 : exactInterval 12 3685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3685 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3685) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3685 : oddCount 3685 12 = 4 ∧ acceleratedOrbit 12 3685 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3685 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3685) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3685.1, data_12_3685.2]

end Collatz.Research.StoppingAtlas.Batch0440
