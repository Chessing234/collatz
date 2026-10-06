import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0967

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7669. -/
theorem bounds_13_7669 : exactInterval 13 7669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7669 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7669) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7669 : oddCount 7669 13 = 7 ∧ acceleratedOrbit 13 7669 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7669 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7669) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7669.1, data_13_7669.2]

/-- Complete interval computation for depth 13, residue 7670. -/
theorem bounds_13_7670 : exactInterval 13 7670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7670 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7670) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7670 : oddCount 7670 13 = 8 ∧ acceleratedOrbit 13 7670 = 6146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7670 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7670) = 3 ^ 8 * m + 6146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7670.1, data_13_7670.2]

/-- Complete interval computation for depth 13, residue 7671. -/
theorem bounds_13_7671 : exactInterval 13 7671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7671 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7671) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7671 : oddCount 7671 13 = 8 ∧ acceleratedOrbit 13 7671 = 6146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7671 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7671) = 3 ^ 8 * m + 6146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7671.1, data_13_7671.2]

/-- Complete interval computation for depth 13, residue 7672. -/
theorem bounds_13_7672 : exactInterval 13 7672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7672 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7672) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7672 : oddCount 7672 13 = 8 ∧ acceleratedOrbit 13 7672 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7672 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7672) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7672.1, data_13_7672.2]

/-- Complete interval computation for depth 13, residue 7673. -/
theorem bounds_13_7673 : exactInterval 13 7673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7673 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7673) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7673 : oddCount 7673 13 = 6 ∧ acceleratedOrbit 13 7673 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7673 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7673) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7673.1, data_13_7673.2]

/-- Complete interval computation for depth 13, residue 7674. -/
theorem bounds_13_7674 : exactInterval 13 7674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7674 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7674) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7674 : oddCount 7674 13 = 8 ∧ acceleratedOrbit 13 7674 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7674 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7674) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7674.1, data_13_7674.2]

/-- Complete interval computation for depth 13, residue 7675. -/
theorem bounds_13_7675 : exactInterval 13 7675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7675 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7675) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7675 : oddCount 7675 13 = 8 ∧ acceleratedOrbit 13 7675 = 6149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7675 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7675) = 3 ^ 8 * m + 6149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7675.1, data_13_7675.2]

/-- Complete interval computation for depth 13, residue 7676. -/
theorem bounds_13_7676 : exactInterval 13 7676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7676 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7676) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7676 : oddCount 7676 13 = 8 ∧ acceleratedOrbit 13 7676 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7676 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7676) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7676.1, data_13_7676.2]

/-- Complete interval computation for depth 13, residue 7677. -/
theorem bounds_13_7677 : exactInterval 13 7677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7677 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7677) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7677 : oddCount 7677 13 = 8 ∧ acceleratedOrbit 13 7677 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7677 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7677) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7677.1, data_13_7677.2]

/-- Complete interval computation for depth 13, residue 7678. -/
theorem bounds_13_7678 : exactInterval 13 7678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7678 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7678) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7678 : oddCount 7678 13 = 11 ∧ acceleratedOrbit 13 7678 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7678 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7678) = 3 ^ 11 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7678.1, data_13_7678.2]

/-- Complete interval computation for depth 13, residue 7679. -/
theorem bounds_13_7679 : exactInterval 13 7679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7679 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7679) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7679 : oddCount 7679 13 = 11 ∧ acceleratedOrbit 13 7679 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7679 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7679) = 3 ^ 11 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7679.1, data_13_7679.2]

/-- Complete interval computation for depth 13, residue 7680. -/
theorem bounds_13_7680 : exactInterval 13 7680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7680 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7680) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7680 : oddCount 7680 13 = 4 ∧ acceleratedOrbit 13 7680 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7680 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7680) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7680.1, data_13_7680.2]

/-- Complete interval computation for depth 13, residue 7681. -/
theorem bounds_13_7681 : exactInterval 13 7681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7681 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7681) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7681 : oddCount 7681 13 = 9 ∧ acceleratedOrbit 13 7681 = 18467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7681 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7681) = 3 ^ 9 * m + 18467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7681.1, data_13_7681.2]

/-- Complete interval computation for depth 13, residue 7682. -/
theorem bounds_13_7682 : exactInterval 13 7682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7682 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7682) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7682 : oddCount 7682 13 = 4 ∧ acceleratedOrbit 13 7682 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7682 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7682) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7682.1, data_13_7682.2]

/-- Complete interval computation for depth 13, residue 7683. -/
theorem bounds_13_7683 : exactInterval 13 7683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7683 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7683) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7683 : oddCount 7683 13 = 4 ∧ acceleratedOrbit 13 7683 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7683 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7683) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7683.1, data_13_7683.2]

/-- Complete interval computation for depth 13, residue 7684. -/
theorem bounds_13_7684 : exactInterval 13 7684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7684 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7684) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7684 : oddCount 7684 13 = 6 ∧ acceleratedOrbit 13 7684 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7684 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7684) = 3 ^ 6 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7684.1, data_13_7684.2]

end Collatz.Research.StoppingAtlas.Batch0967
