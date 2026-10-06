import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0244

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 660. -/
theorem bounds_12_660 : exactInterval 12 660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_660 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 660) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_660 : oddCount 660 12 = 6 ∧ acceleratedOrbit 12 660 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_660 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 660) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_660.1, data_12_660.2]

/-- Complete interval computation for depth 12, residue 661. -/
theorem bounds_12_661 : exactInterval 12 661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_661 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 661) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_661 : oddCount 661 12 = 6 ∧ acceleratedOrbit 12 661 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_661 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 661) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_661.1, data_12_661.2]

/-- Complete interval computation for depth 12, residue 662. -/
theorem bounds_12_662 : exactInterval 12 662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_662 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 662) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_662 : oddCount 662 12 = 5 ∧ acceleratedOrbit 12 662 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_662 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 662) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_662.1, data_12_662.2]

/-- Complete interval computation for depth 12, residue 663. -/
theorem bounds_12_663 : exactInterval 12 663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_663 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 663) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_663 : oddCount 663 12 = 5 ∧ acceleratedOrbit 12 663 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_663 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 663) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_663.1, data_12_663.2]

/-- Complete interval computation for depth 12, residue 664. -/
theorem bounds_12_664 : exactInterval 12 664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_664 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 664) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_664 : oddCount 664 12 = 6 ∧ acceleratedOrbit 12 664 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_664 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 664) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_664.1, data_12_664.2]

/-- Complete interval computation for depth 12, residue 665. -/
theorem bounds_12_665 : exactInterval 12 665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_665 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 665) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_665 : oddCount 665 12 = 6 ∧ acceleratedOrbit 12 665 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_665 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 665) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_665.1, data_12_665.2]

/-- Complete interval computation for depth 12, residue 666. -/
theorem bounds_12_666 : exactInterval 12 666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_666 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 666) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_666 : oddCount 666 12 = 6 ∧ acceleratedOrbit 12 666 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_666 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 666) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_666.1, data_12_666.2]

/-- Complete interval computation for depth 12, residue 667. -/
theorem bounds_12_667 : exactInterval 12 667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_667 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 667) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_667 : oddCount 667 12 = 10 ∧ acceleratedOrbit 12 667 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_667 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 667) = 3 ^ 10 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_667.1, data_12_667.2]

/-- Complete interval computation for depth 12, residue 668. -/
theorem bounds_12_668 : exactInterval 12 668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_668 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 668) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_668 : oddCount 668 12 = 8 ∧ acceleratedOrbit 12 668 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_668 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 668) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_668.1, data_12_668.2]

/-- Complete interval computation for depth 12, residue 669. -/
theorem bounds_12_669 : exactInterval 12 669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_669 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 669) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_669 : oddCount 669 12 = 8 ∧ acceleratedOrbit 12 669 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_669 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 669) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_669.1, data_12_669.2]

/-- Complete interval computation for depth 12, residue 670. -/
theorem bounds_12_670 : exactInterval 12 670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_670 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 670) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_670 : oddCount 670 12 = 8 ∧ acceleratedOrbit 12 670 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_670 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 670) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_670.1, data_12_670.2]

/-- Complete interval computation for depth 12, residue 671. -/
theorem bounds_12_671 : exactInterval 12 671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_671 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 671) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_671 : oddCount 671 12 = 9 ∧ acceleratedOrbit 12 671 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_671 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 671) = 3 ^ 9 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_671.1, data_12_671.2]

/-- Complete interval computation for depth 12, residue 672. -/
theorem bounds_12_672 : exactInterval 12 672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_672 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 672) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_672 : oddCount 672 12 = 2 ∧ acceleratedOrbit 12 672 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_672 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 672) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_672.1, data_12_672.2]

/-- Complete interval computation for depth 12, residue 673. -/
theorem bounds_12_673 : exactInterval 12 673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_673 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 673) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_673 : oddCount 673 12 = 7 ∧ acceleratedOrbit 12 673 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_673 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 673) = 3 ^ 7 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_673.1, data_12_673.2]

/-- Complete interval computation for depth 12, residue 674. -/
theorem bounds_12_674 : exactInterval 12 674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_674 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 674) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_674 : oddCount 674 12 = 7 ∧ acceleratedOrbit 12 674 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_674 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 674) = 3 ^ 7 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_674.1, data_12_674.2]

end Collatz.Research.StoppingAtlas.Batch0244
