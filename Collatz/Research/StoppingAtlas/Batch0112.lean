import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0112

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 680. -/
theorem bounds_11_680 : exactInterval 11 680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_680 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 680) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_680 : oddCount 680 11 = 1 ∧ acceleratedOrbit 11 680 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_680 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 680) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_680.1, data_11_680.2]

/-- Complete interval computation for depth 11, residue 681. -/
theorem bounds_11_681 : exactInterval 11 681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_681 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 681) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_681 : oddCount 681 11 = 10 ∧ acceleratedOrbit 11 681 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_681 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 681) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_681.1, data_11_681.2]

/-- Complete interval computation for depth 11, residue 682. -/
theorem bounds_11_682 : exactInterval 11 682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_682 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 682) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_682 : oddCount 682 11 = 1 ∧ acceleratedOrbit 11 682 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_682 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 682) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_682.1, data_11_682.2]

/-- Complete interval computation for depth 11, residue 683. -/
theorem bounds_11_683 : exactInterval 11 683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_683 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 683) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_683 : oddCount 683 11 = 6 ∧ acceleratedOrbit 11 683 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_683 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 683) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_683.1, data_11_683.2]

/-- Complete interval computation for depth 11, residue 684. -/
theorem bounds_11_684 : exactInterval 11 684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_684 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 684) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_684 : oddCount 684 11 = 5 ∧ acceleratedOrbit 11 684 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_684 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 684) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_684.1, data_11_684.2]

/-- Complete interval computation for depth 11, residue 685. -/
theorem bounds_11_685 : exactInterval 11 685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_685 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 685) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_685 : oddCount 685 11 = 5 ∧ acceleratedOrbit 11 685 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_685 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 685) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_685.1, data_11_685.2]

/-- Complete interval computation for depth 11, residue 686. -/
theorem bounds_11_686 : exactInterval 11 686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_686 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 686) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_686 : oddCount 686 11 = 5 ∧ acceleratedOrbit 11 686 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_686 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 686) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_686.1, data_11_686.2]

/-- Complete interval computation for depth 11, residue 687. -/
theorem bounds_11_687 : exactInterval 11 687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_687 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 687) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_687 : oddCount 687 11 = 6 ∧ acceleratedOrbit 11 687 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_687 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 687) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_687.1, data_11_687.2]

/-- Complete interval computation for depth 11, residue 688. -/
theorem bounds_11_688 : exactInterval 11 688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_688 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 688) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_688 : oddCount 688 11 = 4 ∧ acceleratedOrbit 11 688 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_688 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 688) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_688.1, data_11_688.2]

/-- Complete interval computation for depth 11, residue 689. -/
theorem bounds_11_689 : exactInterval 11 689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_689 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 689) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_689 : oddCount 689 11 = 5 ∧ acceleratedOrbit 11 689 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_689 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 689) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_689.1, data_11_689.2]

/-- Complete interval computation for depth 11, residue 690. -/
theorem bounds_11_690 : exactInterval 11 690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_690 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 690) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_690 : oddCount 690 11 = 5 ∧ acceleratedOrbit 11 690 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_690 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 690) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_690.1, data_11_690.2]

/-- Complete interval computation for depth 11, residue 691. -/
theorem bounds_11_691 : exactInterval 11 691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_691 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 691) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_691 : oddCount 691 11 = 5 ∧ acceleratedOrbit 11 691 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_691 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 691) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_691.1, data_11_691.2]

/-- Complete interval computation for depth 11, residue 692. -/
theorem bounds_11_692 : exactInterval 11 692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_692 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 692) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_692 : oddCount 692 11 = 4 ∧ acceleratedOrbit 11 692 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_692 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 692) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_692.1, data_11_692.2]

/-- Complete interval computation for depth 11, residue 693. -/
theorem bounds_11_693 : exactInterval 11 693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_693 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 693) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_693 : oddCount 693 11 = 4 ∧ acceleratedOrbit 11 693 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_693 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 693) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_693.1, data_11_693.2]

/-- Complete interval computation for depth 11, residue 694. -/
theorem bounds_11_694 : exactInterval 11 694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_694 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 694) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_694 : oddCount 694 11 = 6 ∧ acceleratedOrbit 11 694 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_694 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 694) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_694.1, data_11_694.2]

/-- Complete interval computation for depth 11, residue 695. -/
theorem bounds_11_695 : exactInterval 11 695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_695 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 695) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_695 : oddCount 695 11 = 6 ∧ acceleratedOrbit 11 695 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_695 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 695) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_695.1, data_11_695.2]

end Collatz.Research.StoppingAtlas.Batch0112
