import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0113

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3670. -/
theorem bounds_15_3670 : exactInterval 15 3670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3670 : oddCount 3670 15 = 6 ∧ acceleratedOrbit 15 3670 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3670) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3670.1, data_15_3670.2]

/-- Complete interval computation for depth 15, residue 3671. -/
theorem bounds_15_3671 : exactInterval 15 3671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3671 : oddCount 3671 15 = 6 ∧ acceleratedOrbit 15 3671 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3671) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3671.1, data_15_3671.2]

/-- Complete interval computation for depth 15, residue 3672. -/
theorem bounds_15_3672 : exactInterval 15 3672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3672 : oddCount 3672 15 = 6 ∧ acceleratedOrbit 15 3672 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3672) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3672.1, data_15_3672.2]

/-- Complete interval computation for depth 15, residue 3673. -/
theorem bounds_15_3673 : exactInterval 15 3673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3673 : oddCount 3673 15 = 8 ∧ acceleratedOrbit 15 3673 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3673) = 3 ^ 8 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3673.1, data_15_3673.2]

/-- Complete interval computation for depth 15, residue 3674. -/
theorem bounds_15_3674 : exactInterval 15 3674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3674 : oddCount 3674 15 = 6 ∧ acceleratedOrbit 15 3674 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3674) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3674.1, data_15_3674.2]

/-- Complete interval computation for depth 15, residue 3675. -/
theorem bounds_15_3675 : exactInterval 15 3675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3675 : oddCount 3675 15 = 9 ∧ acceleratedOrbit 15 3675 = 2209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3675) = 3 ^ 9 * m + 2209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3675.1, data_15_3675.2]

/-- Complete interval computation for depth 15, residue 3676. -/
theorem bounds_15_3676 : exactInterval 15 3676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3676 : oddCount 3676 15 = 6 ∧ acceleratedOrbit 15 3676 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3676) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3676.1, data_15_3676.2]

/-- Complete interval computation for depth 15, residue 3677. -/
theorem bounds_15_3677 : exactInterval 15 3677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3677 : oddCount 3677 15 = 6 ∧ acceleratedOrbit 15 3677 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3677) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3677.1, data_15_3677.2]

/-- Complete interval computation for depth 15, residue 3678. -/
theorem bounds_15_3678 : exactInterval 15 3678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3678 : oddCount 3678 15 = 9 ∧ acceleratedOrbit 15 3678 = 2213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3678) = 3 ^ 9 * m + 2213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3678.1, data_15_3678.2]

/-- Complete interval computation for depth 15, residue 3679. -/
theorem bounds_15_3679 : exactInterval 15 3679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3679 : oddCount 3679 15 = 9 ∧ acceleratedOrbit 15 3679 = 2213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3679) = 3 ^ 9 * m + 2213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3679.1, data_15_3679.2]

/-- Complete interval computation for depth 15, residue 3680. -/
theorem bounds_15_3680 : exactInterval 15 3680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3680 : oddCount 3680 15 = 5 ∧ acceleratedOrbit 15 3680 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3680) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3680.1, data_15_3680.2]

/-- Complete interval computation for depth 15, residue 3681. -/
theorem bounds_15_3681 : exactInterval 15 3681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3681 : oddCount 3681 15 = 6 ∧ acceleratedOrbit 15 3681 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3681) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3681.1, data_15_3681.2]

/-- Complete interval computation for depth 15, residue 3682. -/
theorem bounds_15_3682 : exactInterval 15 3682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3682 : oddCount 3682 15 = 6 ∧ acceleratedOrbit 15 3682 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3682) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3682.1, data_15_3682.2]

/-- Complete interval computation for depth 15, residue 3683. -/
theorem bounds_15_3683 : exactInterval 15 3683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3683 : oddCount 3683 15 = 6 ∧ acceleratedOrbit 15 3683 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3683) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3683.1, data_15_3683.2]

/-- Complete interval computation for depth 15, residue 3684. -/
theorem bounds_15_3684 : exactInterval 15 3684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3684 : oddCount 3684 15 = 6 ∧ acceleratedOrbit 15 3684 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3684) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3684.1, data_15_3684.2]

/-- Complete interval computation for depth 15, residue 3685. -/
theorem bounds_15_3685 : exactInterval 15 3685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3685 : oddCount 3685 15 = 6 ∧ acceleratedOrbit 15 3685 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3685) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3685.1, data_15_3685.2]

/-- Complete interval computation for depth 15, residue 3686. -/
theorem bounds_15_3686 : exactInterval 15 3686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3686 : oddCount 3686 15 = 6 ∧ acceleratedOrbit 15 3686 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3686) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3686.1, data_15_3686.2]

/-- Complete interval computation for depth 15, residue 3687. -/
theorem bounds_15_3687 : exactInterval 15 3687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3687 : oddCount 3687 15 = 9 ∧ acceleratedOrbit 15 3687 = 2216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3687) = 3 ^ 9 * m + 2216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3687.1, data_15_3687.2]

/-- Complete interval computation for depth 15, residue 3688. -/
theorem bounds_15_3688 : exactInterval 15 3688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3688 : oddCount 3688 15 = 5 ∧ acceleratedOrbit 15 3688 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3688) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3688.1, data_15_3688.2]

/-- Complete interval computation for depth 15, residue 3689. -/
theorem bounds_15_3689 : exactInterval 15 3689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3689 : oddCount 3689 15 = 10 ∧ acceleratedOrbit 15 3689 = 6652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3689) = 3 ^ 10 * m + 6652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3689.1, data_15_3689.2]

/-- Complete interval computation for depth 15, residue 3690. -/
theorem bounds_15_3690 : exactInterval 15 3690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3690 : oddCount 3690 15 = 5 ∧ acceleratedOrbit 15 3690 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3690) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3690.1, data_15_3690.2]

/-- Complete interval computation for depth 15, residue 3691. -/
theorem bounds_15_3691 : exactInterval 15 3691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3691 : oddCount 3691 15 = 8 ∧ acceleratedOrbit 15 3691 = 740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3691) = 3 ^ 8 * m + 740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3691.1, data_15_3691.2]

/-- Complete interval computation for depth 15, residue 3692. -/
theorem bounds_15_3692 : exactInterval 15 3692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3692 : oddCount 3692 15 = 7 ∧ acceleratedOrbit 15 3692 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3692) = 3 ^ 7 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3692.1, data_15_3692.2]

/-- Complete interval computation for depth 15, residue 3693. -/
theorem bounds_15_3693 : exactInterval 15 3693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3693 : oddCount 3693 15 = 7 ∧ acceleratedOrbit 15 3693 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3693) = 3 ^ 7 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3693.1, data_15_3693.2]

/-- Complete interval computation for depth 15, residue 3694. -/
theorem bounds_15_3694 : exactInterval 15 3694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3694 : oddCount 3694 15 = 7 ∧ acceleratedOrbit 15 3694 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3694) = 3 ^ 7 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3694.1, data_15_3694.2]

/-- Complete interval computation for depth 15, residue 3695. -/
theorem bounds_15_3695 : exactInterval 15 3695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3695 : oddCount 3695 15 = 10 ∧ acceleratedOrbit 15 3695 = 6662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3695) = 3 ^ 10 * m + 6662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3695.1, data_15_3695.2]

/-- Complete interval computation for depth 15, residue 3696. -/
theorem bounds_15_3696 : exactInterval 15 3696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3696 : oddCount 3696 15 = 7 ∧ acceleratedOrbit 15 3696 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3696) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3696.1, data_15_3696.2]

/-- Complete interval computation for depth 15, residue 3697. -/
theorem bounds_15_3697 : exactInterval 15 3697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3697 : oddCount 3697 15 = 5 ∧ acceleratedOrbit 15 3697 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3697) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3697.1, data_15_3697.2]

/-- Complete interval computation for depth 15, residue 3698. -/
theorem bounds_15_3698 : exactInterval 15 3698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3698 : oddCount 3698 15 = 8 ∧ acceleratedOrbit 15 3698 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3698) = 3 ^ 8 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3698.1, data_15_3698.2]

/-- Complete interval computation for depth 15, residue 3699. -/
theorem bounds_15_3699 : exactInterval 15 3699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3699 : oddCount 3699 15 = 8 ∧ acceleratedOrbit 15 3699 = 742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3699) = 3 ^ 8 * m + 742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3699.1, data_15_3699.2]

/-- Complete interval computation for depth 15, residue 3700. -/
theorem bounds_15_3700 : exactInterval 15 3700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3700 : oddCount 3700 15 = 7 ∧ acceleratedOrbit 15 3700 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3700) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3700.1, data_15_3700.2]

/-- Complete interval computation for depth 15, residue 3701. -/
theorem bounds_15_3701 : exactInterval 15 3701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3701 : oddCount 3701 15 = 7 ∧ acceleratedOrbit 15 3701 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3701) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3701.1, data_15_3701.2]

end Collatz.Research.PassageAtlas.Batch0113
