import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0441

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3686. -/
theorem bounds_12_3686 : exactInterval 12 3686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3686 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3686) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3686 : oddCount 3686 12 = 4 ∧ acceleratedOrbit 12 3686 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3686 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3686) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3686.1, data_12_3686.2]

/-- Complete interval computation for depth 12, residue 3687. -/
theorem bounds_12_3687 : exactInterval 12 3687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3687 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3687) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3687 : oddCount 3687 12 = 8 ∧ acceleratedOrbit 12 3687 = 5908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3687 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3687) = 3 ^ 8 * m + 5908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3687.1, data_12_3687.2]

/-- Complete interval computation for depth 12, residue 3688. -/
theorem bounds_12_3688 : exactInterval 12 3688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3688 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3688) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3688 : oddCount 3688 12 = 4 ∧ acceleratedOrbit 12 3688 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3688 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3688) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3688.1, data_12_3688.2]

/-- Complete interval computation for depth 12, residue 3689. -/
theorem bounds_12_3689 : exactInterval 12 3689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3689 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3689) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3689 : oddCount 3689 12 = 9 ∧ acceleratedOrbit 12 3689 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3689 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3689) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3689.1, data_12_3689.2]

/-- Complete interval computation for depth 12, residue 3690. -/
theorem bounds_12_3690 : exactInterval 12 3690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3690 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3690) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3690 : oddCount 3690 12 = 4 ∧ acceleratedOrbit 12 3690 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3690 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3690) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3690.1, data_12_3690.2]

/-- Complete interval computation for depth 12, residue 3691. -/
theorem bounds_12_3691 : exactInterval 12 3691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3691 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3691) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3691 : oddCount 3691 12 = 7 ∧ acceleratedOrbit 12 3691 = 1972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3691 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3691) = 3 ^ 7 * m + 1972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3691.1, data_12_3691.2]

/-- Complete interval computation for depth 12, residue 3692. -/
theorem bounds_12_3692 : exactInterval 12 3692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3692 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3692) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3692 : oddCount 3692 12 = 6 ∧ acceleratedOrbit 12 3692 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3692 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3692) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3692.1, data_12_3692.2]

/-- Complete interval computation for depth 12, residue 3693. -/
theorem bounds_12_3693 : exactInterval 12 3693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3693 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3693) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3693 : oddCount 3693 12 = 6 ∧ acceleratedOrbit 12 3693 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3693 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3693) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3693.1, data_12_3693.2]

/-- Complete interval computation for depth 12, residue 3694. -/
theorem bounds_12_3694 : exactInterval 12 3694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3694 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3694) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3694 : oddCount 3694 12 = 6 ∧ acceleratedOrbit 12 3694 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3694 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3694) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3694.1, data_12_3694.2]

/-- Complete interval computation for depth 12, residue 3695. -/
theorem bounds_12_3695 : exactInterval 12 3695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3695 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3695) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3695 : oddCount 3695 12 = 8 ∧ acceleratedOrbit 12 3695 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3695 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3695) = 3 ^ 8 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3695.1, data_12_3695.2]

/-- Complete interval computation for depth 12, residue 3696. -/
theorem bounds_12_3696 : exactInterval 12 3696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3696 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3696) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3696 : oddCount 3696 12 = 6 ∧ acceleratedOrbit 12 3696 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3696 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3696) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3696.1, data_12_3696.2]

/-- Complete interval computation for depth 12, residue 3697. -/
theorem bounds_12_3697 : exactInterval 12 3697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3697 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3697) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3697 : oddCount 3697 12 = 4 ∧ acceleratedOrbit 12 3697 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3697 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3697) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3697.1, data_12_3697.2]

/-- Complete interval computation for depth 12, residue 3698. -/
theorem bounds_12_3698 : exactInterval 12 3698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3698 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3698) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3698 : oddCount 3698 12 = 6 ∧ acceleratedOrbit 12 3698 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3698 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3698) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3698.1, data_12_3698.2]

/-- Complete interval computation for depth 12, residue 3699. -/
theorem bounds_12_3699 : exactInterval 12 3699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3699 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3699) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3699 : oddCount 3699 12 = 6 ∧ acceleratedOrbit 12 3699 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3699 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3699) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3699.1, data_12_3699.2]

/-- Complete interval computation for depth 12, residue 3700. -/
theorem bounds_12_3700 : exactInterval 12 3700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3700 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3700) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3700 : oddCount 3700 12 = 6 ∧ acceleratedOrbit 12 3700 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3700 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3700) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3700.1, data_12_3700.2]

end Collatz.Research.StoppingAtlas.Batch0441
