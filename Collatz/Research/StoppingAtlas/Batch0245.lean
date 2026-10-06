import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0245

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 675. -/
theorem bounds_12_675 : exactInterval 12 675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_675 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 675) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_675 : oddCount 675 12 = 7 ∧ acceleratedOrbit 12 675 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_675 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 675) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_675.1, data_12_675.2]

/-- Complete interval computation for depth 12, residue 676. -/
theorem bounds_12_676 : exactInterval 12 676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_676 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 676) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_676 : oddCount 676 12 = 8 ∧ acceleratedOrbit 12 676 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_676 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 676) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_676.1, data_12_676.2]

/-- Complete interval computation for depth 12, residue 677. -/
theorem bounds_12_677 : exactInterval 12 677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_677 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 677) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_677 : oddCount 677 12 = 8 ∧ acceleratedOrbit 12 677 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_677 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 677) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_677.1, data_12_677.2]

/-- Complete interval computation for depth 12, residue 678. -/
theorem bounds_12_678 : exactInterval 12 678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_678 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 678) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_678 : oddCount 678 12 = 8 ∧ acceleratedOrbit 12 678 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_678 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 678) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_678.1, data_12_678.2]

/-- Complete interval computation for depth 12, residue 679. -/
theorem bounds_12_679 : exactInterval 12 679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_679 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 679) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_679 : oddCount 679 12 = 8 ∧ acceleratedOrbit 12 679 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_679 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 679) = 3 ^ 8 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_679.1, data_12_679.2]

/-- Complete interval computation for depth 12, residue 680. -/
theorem bounds_12_680 : exactInterval 12 680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_680 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 680) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_680 : oddCount 680 12 = 2 ∧ acceleratedOrbit 12 680 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_680 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 680) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_680.1, data_12_680.2]

/-- Complete interval computation for depth 12, residue 681. -/
theorem bounds_12_681 : exactInterval 12 681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_681 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 681) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_681 : oddCount 681 12 = 10 ∧ acceleratedOrbit 12 681 = 9841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_681 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 681) = 3 ^ 10 * m + 9841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_681.1, data_12_681.2]

/-- Complete interval computation for depth 12, residue 682. -/
theorem bounds_12_682 : exactInterval 12 682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_682 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 682) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_682 : oddCount 682 12 = 2 ∧ acceleratedOrbit 12 682 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_682 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 682) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_682.1, data_12_682.2]

/-- Complete interval computation for depth 12, residue 683. -/
theorem bounds_12_683 : exactInterval 12 683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_683 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 683) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_683 : oddCount 683 12 = 6 ∧ acceleratedOrbit 12 683 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_683 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 683) = 3 ^ 6 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_683.1, data_12_683.2]

/-- Complete interval computation for depth 12, residue 684. -/
theorem bounds_12_684 : exactInterval 12 684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_684 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 684) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_684 : oddCount 684 12 = 5 ∧ acceleratedOrbit 12 684 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_684 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 684) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_684.1, data_12_684.2]

/-- Complete interval computation for depth 12, residue 685. -/
theorem bounds_12_685 : exactInterval 12 685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_685 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 685) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_685 : oddCount 685 12 = 5 ∧ acceleratedOrbit 12 685 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_685 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 685) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_685.1, data_12_685.2]

/-- Complete interval computation for depth 12, residue 686. -/
theorem bounds_12_686 : exactInterval 12 686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_686 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 686) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_686 : oddCount 686 12 = 5 ∧ acceleratedOrbit 12 686 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_686 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 686) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_686.1, data_12_686.2]

/-- Complete interval computation for depth 12, residue 687. -/
theorem bounds_12_687 : exactInterval 12 687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_687 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 687) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_687 : oddCount 687 12 = 7 ∧ acceleratedOrbit 12 687 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_687 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 687) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_687.1, data_12_687.2]

/-- Complete interval computation for depth 12, residue 688. -/
theorem bounds_12_688 : exactInterval 12 688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_688 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 688) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_688 : oddCount 688 12 = 4 ∧ acceleratedOrbit 12 688 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_688 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 688) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_688.1, data_12_688.2]

/-- Complete interval computation for depth 12, residue 689. -/
theorem bounds_12_689 : exactInterval 12 689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_689 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 689) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_689 : oddCount 689 12 = 6 ∧ acceleratedOrbit 12 689 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_689 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 689) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_689.1, data_12_689.2]

/-- Complete interval computation for depth 12, residue 690. -/
theorem bounds_12_690 : exactInterval 12 690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_690 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 690) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_690 : oddCount 690 12 = 6 ∧ acceleratedOrbit 12 690 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_690 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 690) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_690.1, data_12_690.2]

end Collatz.Research.StoppingAtlas.Batch0245
