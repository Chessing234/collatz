import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0111

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 665. -/
theorem bounds_11_665 : exactInterval 11 665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_665 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 665) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_665 : oddCount 665 11 = 6 ∧ acceleratedOrbit 11 665 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_665 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 665) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_665.1, data_11_665.2]

/-- Complete interval computation for depth 11, residue 666. -/
theorem bounds_11_666 : exactInterval 11 666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_666 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 666) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_666 : oddCount 666 11 = 6 ∧ acceleratedOrbit 11 666 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_666 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 666) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_666.1, data_11_666.2]

/-- Complete interval computation for depth 11, residue 667. -/
theorem bounds_11_667 : exactInterval 11 667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_667 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 667) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_667 : oddCount 667 11 = 9 ∧ acceleratedOrbit 11 667 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_667 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 667) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_667.1, data_11_667.2]

/-- Complete interval computation for depth 11, residue 668. -/
theorem bounds_11_668 : exactInterval 11 668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_668 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 668) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_668 : oddCount 668 11 = 7 ∧ acceleratedOrbit 11 668 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_668 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 668) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_668.1, data_11_668.2]

/-- Complete interval computation for depth 11, residue 669. -/
theorem bounds_11_669 : exactInterval 11 669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_669 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 669) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_669 : oddCount 669 11 = 7 ∧ acceleratedOrbit 11 669 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_669 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 669) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_669.1, data_11_669.2]

/-- Complete interval computation for depth 11, residue 670. -/
theorem bounds_11_670 : exactInterval 11 670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_670 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 670) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_670 : oddCount 670 11 = 7 ∧ acceleratedOrbit 11 670 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_670 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 670) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_670.1, data_11_670.2]

/-- Complete interval computation for depth 11, residue 671. -/
theorem bounds_11_671 : exactInterval 11 671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_671 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 671) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_671 : oddCount 671 11 = 8 ∧ acceleratedOrbit 11 671 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_671 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 671) = 3 ^ 8 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_671.1, data_11_671.2]

/-- Complete interval computation for depth 11, residue 672. -/
theorem bounds_11_672 : exactInterval 11 672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_672 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 672) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_672 : oddCount 672 11 = 1 ∧ acceleratedOrbit 11 672 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_672 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 672) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_672.1, data_11_672.2]

/-- Complete interval computation for depth 11, residue 673. -/
theorem bounds_11_673 : exactInterval 11 673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_673 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 673) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_673 : oddCount 673 11 = 7 ∧ acceleratedOrbit 11 673 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_673 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 673) = 3 ^ 7 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_673.1, data_11_673.2]

/-- Complete interval computation for depth 11, residue 674. -/
theorem bounds_11_674 : exactInterval 11 674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_674 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 674) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_674 : oddCount 674 11 = 7 ∧ acceleratedOrbit 11 674 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_674 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 674) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_674.1, data_11_674.2]

/-- Complete interval computation for depth 11, residue 675. -/
theorem bounds_11_675 : exactInterval 11 675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_675 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 675) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_675 : oddCount 675 11 = 7 ∧ acceleratedOrbit 11 675 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_675 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 675) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_675.1, data_11_675.2]

/-- Complete interval computation for depth 11, residue 676. -/
theorem bounds_11_676 : exactInterval 11 676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_676 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 676) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_676 : oddCount 676 11 = 8 ∧ acceleratedOrbit 11 676 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_676 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 676) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_676.1, data_11_676.2]

/-- Complete interval computation for depth 11, residue 677. -/
theorem bounds_11_677 : exactInterval 11 677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_677 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 677) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_677 : oddCount 677 11 = 8 ∧ acceleratedOrbit 11 677 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_677 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 677) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_677.1, data_11_677.2]

/-- Complete interval computation for depth 11, residue 678. -/
theorem bounds_11_678 : exactInterval 11 678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_678 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 678) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_678 : oddCount 678 11 = 8 ∧ acceleratedOrbit 11 678 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_678 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 678) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_678.1, data_11_678.2]

/-- Complete interval computation for depth 11, residue 679. -/
theorem bounds_11_679 : exactInterval 11 679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_679 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 679) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_679 : oddCount 679 11 = 8 ∧ acceleratedOrbit 11 679 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_679 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 679) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_679.1, data_11_679.2]

end Collatz.Research.StoppingAtlas.Batch0111
