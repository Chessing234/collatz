import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0045

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 675. -/
theorem bounds_10_675 : exactInterval 10 675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_675 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 675) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_675 : oddCount 675 10 = 6 ∧ acceleratedOrbit 10 675 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_675 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 675) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_675.1, data_10_675.2]

/-- Complete interval computation for depth 10, residue 676. -/
theorem bounds_10_676 : exactInterval 10 676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_676 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 676) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_676 : oddCount 676 10 = 7 ∧ acceleratedOrbit 10 676 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_676 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 676) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_676.1, data_10_676.2]

/-- Complete interval computation for depth 10, residue 677. -/
theorem bounds_10_677 : exactInterval 10 677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_677 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 677) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_677 : oddCount 677 10 = 7 ∧ acceleratedOrbit 10 677 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_677 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 677) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_677.1, data_10_677.2]

/-- Complete interval computation for depth 10, residue 678. -/
theorem bounds_10_678 : exactInterval 10 678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_678 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 678) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_678 : oddCount 678 10 = 7 ∧ acceleratedOrbit 10 678 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_678 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 678) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_678.1, data_10_678.2]

/-- Complete interval computation for depth 10, residue 679. -/
theorem bounds_10_679 : exactInterval 10 679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_679 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 679) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_679 : oddCount 679 10 = 7 ∧ acceleratedOrbit 10 679 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_679 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 679) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_679.1, data_10_679.2]

/-- Complete interval computation for depth 10, residue 680. -/
theorem bounds_10_680 : exactInterval 10 680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_680 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 680) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_680 : oddCount 680 10 = 1 ∧ acceleratedOrbit 10 680 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_680 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 680) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_680.1, data_10_680.2]

/-- Complete interval computation for depth 10, residue 681. -/
theorem bounds_10_681 : exactInterval 10 681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_681 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 681) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_681 : oddCount 681 10 = 9 ∧ acceleratedOrbit 10 681 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_681 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 681) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_681.1, data_10_681.2]

/-- Complete interval computation for depth 10, residue 682. -/
theorem bounds_10_682 : exactInterval 10 682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_682 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 682) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_682 : oddCount 682 10 = 1 ∧ acceleratedOrbit 10 682 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_682 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 682) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_682.1, data_10_682.2]

/-- Complete interval computation for depth 10, residue 683. -/
theorem bounds_10_683 : exactInterval 10 683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_683 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 683) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_683 : oddCount 683 10 = 6 ∧ acceleratedOrbit 10 683 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_683 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 683) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_683.1, data_10_683.2]

/-- Complete interval computation for depth 10, residue 684. -/
theorem bounds_10_684 : exactInterval 10 684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_684 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 684) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_684 : oddCount 684 10 = 5 ∧ acceleratedOrbit 10 684 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_684 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 684) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_684.1, data_10_684.2]

/-- Complete interval computation for depth 10, residue 685. -/
theorem bounds_10_685 : exactInterval 10 685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_685 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 685) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_685 : oddCount 685 10 = 5 ∧ acceleratedOrbit 10 685 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_685 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 685) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_685.1, data_10_685.2]

/-- Complete interval computation for depth 10, residue 686. -/
theorem bounds_10_686 : exactInterval 10 686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_686 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 686) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_686 : oddCount 686 10 = 5 ∧ acceleratedOrbit 10 686 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_686 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 686) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_686.1, data_10_686.2]

/-- Complete interval computation for depth 10, residue 687. -/
theorem bounds_10_687 : exactInterval 10 687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_687 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 687) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_687 : oddCount 687 10 = 6 ∧ acceleratedOrbit 10 687 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_687 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 687) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_687.1, data_10_687.2]

/-- Complete interval computation for depth 10, residue 688. -/
theorem bounds_10_688 : exactInterval 10 688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_688 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 688) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_688 : oddCount 688 10 = 4 ∧ acceleratedOrbit 10 688 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_688 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 688) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_688.1, data_10_688.2]

/-- Complete interval computation for depth 10, residue 689. -/
theorem bounds_10_689 : exactInterval 10 689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_689 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 689) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_689 : oddCount 689 10 = 4 ∧ acceleratedOrbit 10 689 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_689 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 689) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_689.1, data_10_689.2]

/-- Complete interval computation for depth 10, residue 690. -/
theorem bounds_10_690 : exactInterval 10 690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_690 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 690) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_690 : oddCount 690 10 = 4 ∧ acceleratedOrbit 10 690 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_690 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 690) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_690.1, data_10_690.2]

end Collatz.Research.StoppingAtlas.Batch0045
