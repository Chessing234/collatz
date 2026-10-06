import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0511

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 665. -/
theorem bounds_13_665 : exactInterval 13 665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_665 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 665) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_665 : oddCount 665 13 = 7 ∧ acceleratedOrbit 13 665 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_665 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 665) = 3 ^ 7 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_665.1, data_13_665.2]

/-- Complete interval computation for depth 13, residue 666. -/
theorem bounds_13_666 : exactInterval 13 666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_666 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 666) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_666 : oddCount 666 13 = 7 ∧ acceleratedOrbit 13 666 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_666 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 666) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_666.1, data_13_666.2]

/-- Complete interval computation for depth 13, residue 667. -/
theorem bounds_13_667 : exactInterval 13 667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_667 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 667) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_667 : oddCount 667 13 = 10 ∧ acceleratedOrbit 13 667 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_667 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 667) = 3 ^ 10 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_667.1, data_13_667.2]

/-- Complete interval computation for depth 13, residue 668. -/
theorem bounds_13_668 : exactInterval 13 668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_668 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 668) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_668 : oddCount 668 13 = 9 ∧ acceleratedOrbit 13 668 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_668 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 668) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_668.1, data_13_668.2]

/-- Complete interval computation for depth 13, residue 669. -/
theorem bounds_13_669 : exactInterval 13 669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_669 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 669) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_669 : oddCount 669 13 = 9 ∧ acceleratedOrbit 13 669 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_669 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 669) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_669.1, data_13_669.2]

/-- Complete interval computation for depth 13, residue 670. -/
theorem bounds_13_670 : exactInterval 13 670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_670 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 670) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_670 : oddCount 670 13 = 9 ∧ acceleratedOrbit 13 670 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_670 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 670) = 3 ^ 9 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_670.1, data_13_670.2]

/-- Complete interval computation for depth 13, residue 671. -/
theorem bounds_13_671 : exactInterval 13 671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_671 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 671) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_671 : oddCount 671 13 = 9 ∧ acceleratedOrbit 13 671 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_671 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 671) = 3 ^ 9 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_671.1, data_13_671.2]

/-- Complete interval computation for depth 13, residue 672. -/
theorem bounds_13_672 : exactInterval 13 672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_672 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 672) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_672 : oddCount 672 13 = 2 ∧ acceleratedOrbit 13 672 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_672 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 672) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_672.1, data_13_672.2]

/-- Complete interval computation for depth 13, residue 673. -/
theorem bounds_13_673 : exactInterval 13 673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_673 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 673) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_673 : oddCount 673 13 = 8 ∧ acceleratedOrbit 13 673 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_673 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 673) = 3 ^ 8 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_673.1, data_13_673.2]

/-- Complete interval computation for depth 13, residue 674. -/
theorem bounds_13_674 : exactInterval 13 674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_674 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 674) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_674 : oddCount 674 13 = 7 ∧ acceleratedOrbit 13 674 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_674 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 674) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_674.1, data_13_674.2]

/-- Complete interval computation for depth 13, residue 675. -/
theorem bounds_13_675 : exactInterval 13 675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_675 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 675) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_675 : oddCount 675 13 = 7 ∧ acceleratedOrbit 13 675 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_675 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 675) = 3 ^ 7 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_675.1, data_13_675.2]

/-- Complete interval computation for depth 13, residue 676. -/
theorem bounds_13_676 : exactInterval 13 676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_676 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 676) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_676 : oddCount 676 13 = 9 ∧ acceleratedOrbit 13 676 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_676 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 676) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_676.1, data_13_676.2]

/-- Complete interval computation for depth 13, residue 677. -/
theorem bounds_13_677 : exactInterval 13 677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_677 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 677) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_677 : oddCount 677 13 = 9 ∧ acceleratedOrbit 13 677 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_677 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 677) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_677.1, data_13_677.2]

/-- Complete interval computation for depth 13, residue 678. -/
theorem bounds_13_678 : exactInterval 13 678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_678 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 678) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_678 : oddCount 678 13 = 9 ∧ acceleratedOrbit 13 678 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_678 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 678) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_678.1, data_13_678.2]

/-- Complete interval computation for depth 13, residue 679. -/
theorem bounds_13_679 : exactInterval 13 679 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_679 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 679) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_679 : oddCount 679 13 = 8 ∧ acceleratedOrbit 13 679 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_679 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 679) = 3 ^ 8 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_679.1, data_13_679.2]

end Collatz.Research.StoppingAtlas.Batch0511
