import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0296

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9666. -/
theorem bounds_15_9666 : exactInterval 15 9666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9666 : oddCount 9666 15 = 10 ∧ acceleratedOrbit 15 9666 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9666) = 3 ^ 10 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9666.1, data_15_9666.2]

/-- Complete interval computation for depth 15, residue 9667. -/
theorem bounds_15_9667 : exactInterval 15 9667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9667 : oddCount 9667 15 = 10 ∧ acceleratedOrbit 15 9667 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9667) = 3 ^ 10 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9667.1, data_15_9667.2]

/-- Complete interval computation for depth 15, residue 9668. -/
theorem bounds_15_9668 : exactInterval 15 9668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9668 : oddCount 9668 15 = 3 ∧ acceleratedOrbit 15 9668 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9668) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9668.1, data_15_9668.2]

/-- Complete interval computation for depth 15, residue 9669. -/
theorem bounds_15_9669 : exactInterval 15 9669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9669 : oddCount 9669 15 = 3 ∧ acceleratedOrbit 15 9669 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9669) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9669.1, data_15_9669.2]

/-- Complete interval computation for depth 15, residue 9670. -/
theorem bounds_15_9670 : exactInterval 15 9670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9670 : oddCount 9670 15 = 3 ∧ acceleratedOrbit 15 9670 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9670) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9670.1, data_15_9670.2]

/-- Complete interval computation for depth 15, residue 9671. -/
theorem bounds_15_9671 : exactInterval 15 9671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9671 : oddCount 9671 15 = 8 ∧ acceleratedOrbit 15 9671 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9671) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9671.1, data_15_9671.2]

/-- Complete interval computation for depth 15, residue 9672. -/
theorem bounds_15_9672 : exactInterval 15 9672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9672 : oddCount 9672 15 = 8 ∧ acceleratedOrbit 15 9672 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9672) = 3 ^ 8 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9672.1, data_15_9672.2]

/-- Complete interval computation for depth 15, residue 9673. -/
theorem bounds_15_9673 : exactInterval 15 9673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9673 : oddCount 9673 15 = 7 ∧ acceleratedOrbit 15 9673 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9673) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9673.1, data_15_9673.2]

/-- Complete interval computation for depth 15, residue 9674. -/
theorem bounds_15_9674 : exactInterval 15 9674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9674 : oddCount 9674 15 = 8 ∧ acceleratedOrbit 15 9674 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9674) = 3 ^ 8 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9674.1, data_15_9674.2]

/-- Complete interval computation for depth 15, residue 9675. -/
theorem bounds_15_9675 : exactInterval 15 9675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9675 : oddCount 9675 15 = 8 ∧ acceleratedOrbit 15 9675 = 1939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9675) = 3 ^ 8 * m + 1939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9675.1, data_15_9675.2]

/-- Complete interval computation for depth 15, residue 9676. -/
theorem bounds_15_9676 : exactInterval 15 9676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9676 : oddCount 9676 15 = 8 ∧ acceleratedOrbit 15 9676 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9676) = 3 ^ 8 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9676.1, data_15_9676.2]

/-- Complete interval computation for depth 15, residue 9677. -/
theorem bounds_15_9677 : exactInterval 15 9677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9677 : oddCount 9677 15 = 8 ∧ acceleratedOrbit 15 9677 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9677) = 3 ^ 8 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9677.1, data_15_9677.2]

/-- Complete interval computation for depth 15, residue 9678. -/
theorem bounds_15_9678 : exactInterval 15 9678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9678 : oddCount 9678 15 = 9 ∧ acceleratedOrbit 15 9678 = 5815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9678) = 3 ^ 9 * m + 5815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9678.1, data_15_9678.2]

/-- Complete interval computation for depth 15, residue 9679. -/
theorem bounds_15_9679 : exactInterval 15 9679 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9679) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9679 : oddCount 9679 15 = 9 ∧ acceleratedOrbit 15 9679 = 5815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9679) = 3 ^ 9 * m + 5815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9679.1, data_15_9679.2]

/-- Complete interval computation for depth 15, residue 9680. -/
theorem bounds_15_9680 : exactInterval 15 9680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9680 : oddCount 9680 15 = 3 ∧ acceleratedOrbit 15 9680 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9680) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9680.1, data_15_9680.2]

/-- Complete interval computation for depth 15, residue 9681. -/
theorem bounds_15_9681 : exactInterval 15 9681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9681 : oddCount 9681 15 = 8 ∧ acceleratedOrbit 15 9681 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9681) = 3 ^ 8 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9681.1, data_15_9681.2]

/-- Complete interval computation for depth 15, residue 9682. -/
theorem bounds_15_9682 : exactInterval 15 9682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9682 : oddCount 9682 15 = 10 ∧ acceleratedOrbit 15 9682 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9682) = 3 ^ 10 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9682.1, data_15_9682.2]

/-- Complete interval computation for depth 15, residue 9683. -/
theorem bounds_15_9683 : exactInterval 15 9683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9683 : oddCount 9683 15 = 10 ∧ acceleratedOrbit 15 9683 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9683) = 3 ^ 10 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9683.1, data_15_9683.2]

/-- Complete interval computation for depth 15, residue 9684. -/
theorem bounds_15_9684 : exactInterval 15 9684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9684 : oddCount 9684 15 = 3 ∧ acceleratedOrbit 15 9684 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9684) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9684.1, data_15_9684.2]

/-- Complete interval computation for depth 15, residue 9685. -/
theorem bounds_15_9685 : exactInterval 15 9685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9685 : oddCount 9685 15 = 3 ∧ acceleratedOrbit 15 9685 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9685) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9685.1, data_15_9685.2]

/-- Complete interval computation for depth 15, residue 9686. -/
theorem bounds_15_9686 : exactInterval 15 9686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9686 : oddCount 9686 15 = 9 ∧ acceleratedOrbit 15 9686 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9686) = 3 ^ 9 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9686.1, data_15_9686.2]

/-- Complete interval computation for depth 15, residue 9687. -/
theorem bounds_15_9687 : exactInterval 15 9687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9687 : oddCount 9687 15 = 9 ∧ acceleratedOrbit 15 9687 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9687) = 3 ^ 9 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9687.1, data_15_9687.2]

/-- Complete interval computation for depth 15, residue 9688. -/
theorem bounds_15_9688 : exactInterval 15 9688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9688 : oddCount 9688 15 = 9 ∧ acceleratedOrbit 15 9688 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9688) = 3 ^ 9 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9688.1, data_15_9688.2]

/-- Complete interval computation for depth 15, residue 9689. -/
theorem bounds_15_9689 : exactInterval 15 9689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9689 : oddCount 9689 15 = 9 ∧ acceleratedOrbit 15 9689 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9689) = 3 ^ 9 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9689.1, data_15_9689.2]

/-- Complete interval computation for depth 15, residue 9690. -/
theorem bounds_15_9690 : exactInterval 15 9690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9690 : oddCount 9690 15 = 9 ∧ acceleratedOrbit 15 9690 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9690) = 3 ^ 9 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9690.1, data_15_9690.2]

/-- Complete interval computation for depth 15, residue 9691. -/
theorem bounds_15_9691 : exactInterval 15 9691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9691 : oddCount 9691 15 = 8 ∧ acceleratedOrbit 15 9691 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9691) = 3 ^ 8 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9691.1, data_15_9691.2]

/-- Complete interval computation for depth 15, residue 9692. -/
theorem bounds_15_9692 : exactInterval 15 9692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9692 : oddCount 9692 15 = 9 ∧ acceleratedOrbit 15 9692 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9692) = 3 ^ 9 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9692.1, data_15_9692.2]

/-- Complete interval computation for depth 15, residue 9693. -/
theorem bounds_15_9693 : exactInterval 15 9693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9693 : oddCount 9693 15 = 9 ∧ acceleratedOrbit 15 9693 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9693) = 3 ^ 9 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9693.1, data_15_9693.2]

/-- Complete interval computation for depth 15, residue 9694. -/
theorem bounds_15_9694 : exactInterval 15 9694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9694 : oddCount 9694 15 = 11 ∧ acceleratedOrbit 15 9694 = 52420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9694) = 3 ^ 11 * m + 52420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9694.1, data_15_9694.2]

/-- Complete interval computation for depth 15, residue 9695. -/
theorem bounds_15_9695 : exactInterval 15 9695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9695 : oddCount 9695 15 = 11 ∧ acceleratedOrbit 15 9695 = 52420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9695) = 3 ^ 11 * m + 52420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9695.1, data_15_9695.2]

/-- Complete interval computation for depth 15, residue 9696. -/
theorem bounds_15_9696 : exactInterval 15 9696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9696 : oddCount 9696 15 = 7 ∧ acceleratedOrbit 15 9696 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9696) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9696.1, data_15_9696.2]

/-- Complete interval computation for depth 15, residue 9697. -/
theorem bounds_15_9697 : exactInterval 15 9697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9697 : oddCount 9697 15 = 9 ∧ acceleratedOrbit 15 9697 = 5827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9697) = 3 ^ 9 * m + 5827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9697.1, data_15_9697.2]

/-- Complete interval computation for depth 15, residue 9698. -/
theorem bounds_15_9698 : exactInterval 15 9698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9698 : oddCount 9698 15 = 3 ∧ acceleratedOrbit 15 9698 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9698) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9698.1, data_15_9698.2]

end Collatz.Research.PassageAtlas.Batch0296
