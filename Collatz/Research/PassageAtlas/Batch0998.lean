import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0998

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32669. -/
theorem bounds_15_32669 : exactInterval 15 32669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32669 : oddCount 32669 15 = 9 ∧ acceleratedOrbit 15 32669 = 19628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32669) = 3 ^ 9 * m + 19628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32669.1, data_15_32669.2]

/-- Complete interval computation for depth 15, residue 32670. -/
theorem bounds_15_32670 : exactInterval 15 32670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32670 : oddCount 32670 15 = 9 ∧ acceleratedOrbit 15 32670 = 19628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32670) = 3 ^ 9 * m + 19628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32670.1, data_15_32670.2]

/-- Complete interval computation for depth 15, residue 32671. -/
theorem bounds_15_32671 : exactInterval 15 32671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32671 : oddCount 32671 15 = 10 ∧ acceleratedOrbit 15 32671 = 58877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32671) = 3 ^ 10 * m + 58877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32671.1, data_15_32671.2]

/-- Complete interval computation for depth 15, residue 32672. -/
theorem bounds_15_32672 : exactInterval 15 32672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32672 : oddCount 32672 15 = 8 ∧ acceleratedOrbit 15 32672 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32672) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32672.1, data_15_32672.2]

/-- Complete interval computation for depth 15, residue 32673. -/
theorem bounds_15_32673 : exactInterval 15 32673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32673 : oddCount 32673 15 = 6 ∧ acceleratedOrbit 15 32673 = 727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32673) = 3 ^ 6 * m + 727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32673.1, data_15_32673.2]

/-- Complete interval computation for depth 15, residue 32674. -/
theorem bounds_15_32674 : exactInterval 15 32674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32674 : oddCount 32674 15 = 7 ∧ acceleratedOrbit 15 32674 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32674) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32674.1, data_15_32674.2]

/-- Complete interval computation for depth 15, residue 32675. -/
theorem bounds_15_32675 : exactInterval 15 32675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32675 : oddCount 32675 15 = 7 ∧ acceleratedOrbit 15 32675 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32675) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32675.1, data_15_32675.2]

/-- Complete interval computation for depth 15, residue 32676. -/
theorem bounds_15_32676 : exactInterval 15 32676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32676 : oddCount 32676 15 = 8 ∧ acceleratedOrbit 15 32676 = 6544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32676) = 3 ^ 8 * m + 6544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32676.1, data_15_32676.2]

/-- Complete interval computation for depth 15, residue 32677. -/
theorem bounds_15_32677 : exactInterval 15 32677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32677 : oddCount 32677 15 = 8 ∧ acceleratedOrbit 15 32677 = 6544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32677) = 3 ^ 8 * m + 6544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32677.1, data_15_32677.2]

/-- Complete interval computation for depth 15, residue 32678. -/
theorem bounds_15_32678 : exactInterval 15 32678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32678 : oddCount 32678 15 = 8 ∧ acceleratedOrbit 15 32678 = 6544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32678) = 3 ^ 8 * m + 6544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32678.1, data_15_32678.2]

/-- Complete interval computation for depth 15, residue 32679. -/
theorem bounds_15_32679 : exactInterval 15 32679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32679 : oddCount 32679 15 = 9 ∧ acceleratedOrbit 15 32679 = 19631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32679) = 3 ^ 9 * m + 19631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32679.1, data_15_32679.2]

/-- Complete interval computation for depth 15, residue 32680. -/
theorem bounds_15_32680 : exactInterval 15 32680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32680 : oddCount 32680 15 = 8 ∧ acceleratedOrbit 15 32680 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32680) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32680.1, data_15_32680.2]

/-- Complete interval computation for depth 15, residue 32681. -/
theorem bounds_15_32681 : exactInterval 15 32681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32681 : oddCount 32681 15 = 11 ∧ acceleratedOrbit 15 32681 = 176687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32681) = 3 ^ 11 * m + 176687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32681.1, data_15_32681.2]

/-- Complete interval computation for depth 15, residue 32682. -/
theorem bounds_15_32682 : exactInterval 15 32682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32682 : oddCount 32682 15 = 8 ∧ acceleratedOrbit 15 32682 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32682) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32682.1, data_15_32682.2]

/-- Complete interval computation for depth 15, residue 32683. -/
theorem bounds_15_32683 : exactInterval 15 32683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32683 : oddCount 32683 15 = 8 ∧ acceleratedOrbit 15 32683 = 6545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32683) = 3 ^ 8 * m + 6545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32683.1, data_15_32683.2]

/-- Complete interval computation for depth 15, residue 32684. -/
theorem bounds_15_32684 : exactInterval 15 32684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32684 : oddCount 32684 15 = 10 ∧ acceleratedOrbit 15 32684 = 58913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32684) = 3 ^ 10 * m + 58913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32684.1, data_15_32684.2]

/-- Complete interval computation for depth 15, residue 32685. -/
theorem bounds_15_32685 : exactInterval 15 32685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32685 : oddCount 32685 15 = 10 ∧ acceleratedOrbit 15 32685 = 58913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32685) = 3 ^ 10 * m + 58913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32685.1, data_15_32685.2]

/-- Complete interval computation for depth 15, residue 32686. -/
theorem bounds_15_32686 : exactInterval 15 32686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32686 : oddCount 32686 15 = 10 ∧ acceleratedOrbit 15 32686 = 58913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32686) = 3 ^ 10 * m + 58913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32686.1, data_15_32686.2]

/-- Complete interval computation for depth 15, residue 32687. -/
theorem bounds_15_32687 : exactInterval 15 32687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32687 : oddCount 32687 15 = 7 ∧ acceleratedOrbit 15 32687 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32687) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32687.1, data_15_32687.2]

/-- Complete interval computation for depth 15, residue 32688. -/
theorem bounds_15_32688 : exactInterval 15 32688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32688 : oddCount 32688 15 = 8 ∧ acceleratedOrbit 15 32688 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32688) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32688.1, data_15_32688.2]

/-- Complete interval computation for depth 15, residue 32689. -/
theorem bounds_15_32689 : exactInterval 15 32689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32689 : oddCount 32689 15 = 7 ∧ acceleratedOrbit 15 32689 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32689) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32689.1, data_15_32689.2]

/-- Complete interval computation for depth 15, residue 32690. -/
theorem bounds_15_32690 : exactInterval 15 32690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32690 : oddCount 32690 15 = 7 ∧ acceleratedOrbit 15 32690 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32690) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32690.1, data_15_32690.2]

/-- Complete interval computation for depth 15, residue 32691. -/
theorem bounds_15_32691 : exactInterval 15 32691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32691 : oddCount 32691 15 = 7 ∧ acceleratedOrbit 15 32691 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32691) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32691.1, data_15_32691.2]

/-- Complete interval computation for depth 15, residue 32692. -/
theorem bounds_15_32692 : exactInterval 15 32692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32692 : oddCount 32692 15 = 8 ∧ acceleratedOrbit 15 32692 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32692) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32692.1, data_15_32692.2]

/-- Complete interval computation for depth 15, residue 32693. -/
theorem bounds_15_32693 : exactInterval 15 32693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32693 : oddCount 32693 15 = 8 ∧ acceleratedOrbit 15 32693 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32693) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32693.1, data_15_32693.2]

/-- Complete interval computation for depth 15, residue 32694. -/
theorem bounds_15_32694 : exactInterval 15 32694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32694 : oddCount 32694 15 = 9 ∧ acceleratedOrbit 15 32694 = 19642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32694) = 3 ^ 9 * m + 19642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32694.1, data_15_32694.2]

/-- Complete interval computation for depth 15, residue 32695. -/
theorem bounds_15_32695 : exactInterval 15 32695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32695 : oddCount 32695 15 = 9 ∧ acceleratedOrbit 15 32695 = 19642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32695) = 3 ^ 9 * m + 19642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32695.1, data_15_32695.2]

/-- Complete interval computation for depth 15, residue 32696. -/
theorem bounds_15_32696 : exactInterval 15 32696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32696 : oddCount 32696 15 = 8 ∧ acceleratedOrbit 15 32696 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32696) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32696.1, data_15_32696.2]

/-- Complete interval computation for depth 15, residue 32697. -/
theorem bounds_15_32697 : exactInterval 15 32697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32697 : oddCount 32697 15 = 6 ∧ acceleratedOrbit 15 32697 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32697) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32697.1, data_15_32697.2]

/-- Complete interval computation for depth 15, residue 32698. -/
theorem bounds_15_32698 : exactInterval 15 32698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32698 : oddCount 32698 15 = 8 ∧ acceleratedOrbit 15 32698 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32698) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32698.1, data_15_32698.2]

/-- Complete interval computation for depth 15, residue 32699. -/
theorem bounds_15_32699 : exactInterval 15 32699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32699 : oddCount 32699 15 = 6 ∧ acceleratedOrbit 15 32699 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32699) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32699.1, data_15_32699.2]

/-- Complete interval computation for depth 15, residue 32700. -/
theorem bounds_15_32700 : exactInterval 15 32700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32700 : oddCount 32700 15 = 9 ∧ acceleratedOrbit 15 32700 = 19646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32700) = 3 ^ 9 * m + 19646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32700.1, data_15_32700.2]

/-- Complete interval computation for depth 15, residue 32701. -/
theorem bounds_15_32701 : exactInterval 15 32701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32701 : oddCount 32701 15 = 9 ∧ acceleratedOrbit 15 32701 = 19646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32701) = 3 ^ 9 * m + 19646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32701.1, data_15_32701.2]

end Collatz.Research.PassageAtlas.Batch0998
