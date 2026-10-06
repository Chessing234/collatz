import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0512

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 680. -/
theorem bounds_13_680 : exactInterval 13 680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_680 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 680) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_680 : oddCount 680 13 = 2 ∧ acceleratedOrbit 13 680 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_680 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 680) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_680.1, data_13_680.2]

/-- Complete interval computation for depth 13, residue 681. -/
theorem bounds_13_681 : exactInterval 13 681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_681 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 681) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_681 : oddCount 681 13 = 11 ∧ acceleratedOrbit 13 681 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_681 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 681) = 3 ^ 11 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_681.1, data_13_681.2]

/-- Complete interval computation for depth 13, residue 682. -/
theorem bounds_13_682 : exactInterval 13 682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_682 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 682) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_682 : oddCount 682 13 = 2 ∧ acceleratedOrbit 13 682 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_682 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 682) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_682.1, data_13_682.2]

/-- Complete interval computation for depth 13, residue 683. -/
theorem bounds_13_683 : exactInterval 13 683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_683 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 683) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_683 : oddCount 683 13 = 6 ∧ acceleratedOrbit 13 683 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_683 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 683) = 3 ^ 6 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_683.1, data_13_683.2]

/-- Complete interval computation for depth 13, residue 684. -/
theorem bounds_13_684 : exactInterval 13 684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_684 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 684) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_684 : oddCount 684 13 = 6 ∧ acceleratedOrbit 13 684 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_684 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 684) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_684.1, data_13_684.2]

/-- Complete interval computation for depth 13, residue 685. -/
theorem bounds_13_685 : exactInterval 13 685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_685 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 685) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_685 : oddCount 685 13 = 6 ∧ acceleratedOrbit 13 685 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_685 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 685) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_685.1, data_13_685.2]

/-- Complete interval computation for depth 13, residue 686. -/
theorem bounds_13_686 : exactInterval 13 686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_686 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 686) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_686 : oddCount 686 13 = 6 ∧ acceleratedOrbit 13 686 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_686 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 686) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_686.1, data_13_686.2]

/-- Complete interval computation for depth 13, residue 687. -/
theorem bounds_13_687 : exactInterval 13 687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_687 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 687) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_687 : oddCount 687 13 = 7 ∧ acceleratedOrbit 13 687 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_687 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 687) = 3 ^ 7 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_687.1, data_13_687.2]

/-- Complete interval computation for depth 13, residue 688. -/
theorem bounds_13_688 : exactInterval 13 688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_688 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 688) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_688 : oddCount 688 13 = 4 ∧ acceleratedOrbit 13 688 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_688 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 688) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_688.1, data_13_688.2]

/-- Complete interval computation for depth 13, residue 689. -/
theorem bounds_13_689 : exactInterval 13 689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_689 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 689) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_689 : oddCount 689 13 = 7 ∧ acceleratedOrbit 13 689 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_689 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 689) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_689.1, data_13_689.2]

/-- Complete interval computation for depth 13, residue 690. -/
theorem bounds_13_690 : exactInterval 13 690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_690 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 690) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_690 : oddCount 690 13 = 7 ∧ acceleratedOrbit 13 690 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_690 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 690) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_690.1, data_13_690.2]

/-- Complete interval computation for depth 13, residue 691. -/
theorem bounds_13_691 : exactInterval 13 691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_691 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 691) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_691 : oddCount 691 13 = 7 ∧ acceleratedOrbit 13 691 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_691 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 691) = 3 ^ 7 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_691.1, data_13_691.2]

/-- Complete interval computation for depth 13, residue 692. -/
theorem bounds_13_692 : exactInterval 13 692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_692 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 692) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_692 : oddCount 692 13 = 4 ∧ acceleratedOrbit 13 692 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_692 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 692) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_692.1, data_13_692.2]

/-- Complete interval computation for depth 13, residue 693. -/
theorem bounds_13_693 : exactInterval 13 693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_693 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 693) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_693 : oddCount 693 13 = 4 ∧ acceleratedOrbit 13 693 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_693 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 693) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_693.1, data_13_693.2]

/-- Complete interval computation for depth 13, residue 694. -/
theorem bounds_13_694 : exactInterval 13 694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_694 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 694) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_694 : oddCount 694 13 = 6 ∧ acceleratedOrbit 13 694 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_694 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 694) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_694.1, data_13_694.2]

/-- Complete interval computation for depth 13, residue 695. -/
theorem bounds_13_695 : exactInterval 13 695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_695 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 695) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_695 : oddCount 695 13 = 6 ∧ acceleratedOrbit 13 695 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_695 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 695) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_695.1, data_13_695.2]

end Collatz.Research.StoppingAtlas.Batch0512
