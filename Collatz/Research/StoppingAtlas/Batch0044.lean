import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0044

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 660. -/
theorem bounds_10_660 : exactInterval 10 660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_660 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 660) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_660 : oddCount 660 10 = 5 ∧ acceleratedOrbit 10 660 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_660 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 660) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_660.1, data_10_660.2]

/-- Complete interval computation for depth 10, residue 661. -/
theorem bounds_10_661 : exactInterval 10 661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_661 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 661) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_661 : oddCount 661 10 = 5 ∧ acceleratedOrbit 10 661 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_661 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 661) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_661.1, data_10_661.2]

/-- Complete interval computation for depth 10, residue 662. -/
theorem bounds_10_662 : exactInterval 10 662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_662 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 662) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_662 : oddCount 662 10 = 4 ∧ acceleratedOrbit 10 662 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_662 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 662) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_662.1, data_10_662.2]

/-- Complete interval computation for depth 10, residue 663. -/
theorem bounds_10_663 : exactInterval 10 663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_663 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 663) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_663 : oddCount 663 10 = 4 ∧ acceleratedOrbit 10 663 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_663 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 663) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_663.1, data_10_663.2]

/-- Complete interval computation for depth 10, residue 664. -/
theorem bounds_10_664 : exactInterval 10 664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_664 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 664) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_664 : oddCount 664 10 = 5 ∧ acceleratedOrbit 10 664 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_664 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 664) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_664.1, data_10_664.2]

/-- Complete interval computation for depth 10, residue 665. -/
theorem bounds_10_665 : exactInterval 10 665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_665 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 665) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_665 : oddCount 665 10 = 6 ∧ acceleratedOrbit 10 665 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_665 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 665) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_665.1, data_10_665.2]

/-- Complete interval computation for depth 10, residue 666. -/
theorem bounds_10_666 : exactInterval 10 666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_666 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 666) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_666 : oddCount 666 10 = 5 ∧ acceleratedOrbit 10 666 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_666 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 666) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_666.1, data_10_666.2]

/-- Complete interval computation for depth 10, residue 667. -/
theorem bounds_10_667 : exactInterval 10 667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_667 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 667) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_667 : oddCount 667 10 = 8 ∧ acceleratedOrbit 10 667 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_667 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 667) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_667.1, data_10_667.2]

/-- Complete interval computation for depth 10, residue 668. -/
theorem bounds_10_668 : exactInterval 10 668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_668 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 668) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_668 : oddCount 668 10 = 6 ∧ acceleratedOrbit 10 668 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_668 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 668) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_668.1, data_10_668.2]

/-- Complete interval computation for depth 10, residue 669. -/
theorem bounds_10_669 : exactInterval 10 669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_669 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 669) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_669 : oddCount 669 10 = 6 ∧ acceleratedOrbit 10 669 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_669 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 669) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_669.1, data_10_669.2]

/-- Complete interval computation for depth 10, residue 670. -/
theorem bounds_10_670 : exactInterval 10 670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_670 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 670) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_670 : oddCount 670 10 = 6 ∧ acceleratedOrbit 10 670 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_670 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 670) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_670.1, data_10_670.2]

/-- Complete interval computation for depth 10, residue 671. -/
theorem bounds_10_671 : exactInterval 10 671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_671 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 671) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_671 : oddCount 671 10 = 8 ∧ acceleratedOrbit 10 671 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_671 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 671) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_671.1, data_10_671.2]

/-- Complete interval computation for depth 10, residue 672. -/
theorem bounds_10_672 : exactInterval 10 672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_672 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 672) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_672 : oddCount 672 10 = 1 ∧ acceleratedOrbit 10 672 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_672 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 672) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_672.1, data_10_672.2]

/-- Complete interval computation for depth 10, residue 673. -/
theorem bounds_10_673 : exactInterval 10 673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_673 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 673) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_673 : oddCount 673 10 = 6 ∧ acceleratedOrbit 10 673 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_673 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 673) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_673.1, data_10_673.2]

/-- Complete interval computation for depth 10, residue 674. -/
theorem bounds_10_674 : exactInterval 10 674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_674 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 674) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_674 : oddCount 674 10 = 6 ∧ acceleratedOrbit 10 674 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_674 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 674) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_674.1, data_10_674.2]

end Collatz.Research.StoppingAtlas.Batch0044
