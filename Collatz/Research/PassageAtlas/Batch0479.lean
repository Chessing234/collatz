import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0479

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15663. -/
theorem bounds_15_15663 : exactInterval 15 15663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15663 : oddCount 15663 15 = 11 ∧ acceleratedOrbit 15 15663 = 84685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15663) = 3 ^ 11 * m + 84685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15663.1, data_15_15663.2]

/-- Complete interval computation for depth 15, residue 15664. -/
theorem bounds_15_15664 : exactInterval 15 15664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15664 : oddCount 15664 15 = 7 ∧ acceleratedOrbit 15 15664 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15664) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15664.1, data_15_15664.2]

/-- Complete interval computation for depth 15, residue 15665. -/
theorem bounds_15_15665 : exactInterval 15 15665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15665 : oddCount 15665 15 = 9 ∧ acceleratedOrbit 15 15665 = 9416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15665) = 3 ^ 9 * m + 9416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15665.1, data_15_15665.2]

/-- Complete interval computation for depth 15, residue 15666. -/
theorem bounds_15_15666 : exactInterval 15 15666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15666 : oddCount 15666 15 = 9 ∧ acceleratedOrbit 15 15666 = 9416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15666) = 3 ^ 9 * m + 9416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15666.1, data_15_15666.2]

/-- Complete interval computation for depth 15, residue 15667. -/
theorem bounds_15_15667 : exactInterval 15 15667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15667 : oddCount 15667 15 = 9 ∧ acceleratedOrbit 15 15667 = 9416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15667) = 3 ^ 9 * m + 9416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15667.1, data_15_15667.2]

/-- Complete interval computation for depth 15, residue 15668. -/
theorem bounds_15_15668 : exactInterval 15 15668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15668 : oddCount 15668 15 = 7 ∧ acceleratedOrbit 15 15668 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15668) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15668.1, data_15_15668.2]

/-- Complete interval computation for depth 15, residue 15669. -/
theorem bounds_15_15669 : exactInterval 15 15669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15669 : oddCount 15669 15 = 7 ∧ acceleratedOrbit 15 15669 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15669) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15669.1, data_15_15669.2]

/-- Complete interval computation for depth 15, residue 15670. -/
theorem bounds_15_15670 : exactInterval 15 15670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15670 : oddCount 15670 15 = 10 ∧ acceleratedOrbit 15 15670 = 28244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15670) = 3 ^ 10 * m + 28244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15670.1, data_15_15670.2]

/-- Complete interval computation for depth 15, residue 15671. -/
theorem bounds_15_15671 : exactInterval 15 15671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15671 : oddCount 15671 15 = 10 ∧ acceleratedOrbit 15 15671 = 28244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15671) = 3 ^ 10 * m + 28244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15671.1, data_15_15671.2]

/-- Complete interval computation for depth 15, residue 15672. -/
theorem bounds_15_15672 : exactInterval 15 15672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15672 : oddCount 15672 15 = 9 ∧ acceleratedOrbit 15 15672 = 9422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15672) = 3 ^ 9 * m + 9422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15672.1, data_15_15672.2]

/-- Complete interval computation for depth 15, residue 15673. -/
theorem bounds_15_15673 : exactInterval 15 15673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15673 : oddCount 15673 15 = 11 ∧ acceleratedOrbit 15 15673 = 84746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15673) = 3 ^ 11 * m + 84746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15673.1, data_15_15673.2]

/-- Complete interval computation for depth 15, residue 15674. -/
theorem bounds_15_15674 : exactInterval 15 15674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15674 : oddCount 15674 15 = 9 ∧ acceleratedOrbit 15 15674 = 9422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15674) = 3 ^ 9 * m + 9422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15674.1, data_15_15674.2]

/-- Complete interval computation for depth 15, residue 15675. -/
theorem bounds_15_15675 : exactInterval 15 15675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15675 : oddCount 15675 15 = 6 ∧ acceleratedOrbit 15 15675 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15675) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15675.1, data_15_15675.2]

/-- Complete interval computation for depth 15, residue 15676. -/
theorem bounds_15_15676 : exactInterval 15 15676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15676 : oddCount 15676 15 = 9 ∧ acceleratedOrbit 15 15676 = 9422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15676) = 3 ^ 9 * m + 9422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15676.1, data_15_15676.2]

/-- Complete interval computation for depth 15, residue 15677. -/
theorem bounds_15_15677 : exactInterval 15 15677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15677 : oddCount 15677 15 = 9 ∧ acceleratedOrbit 15 15677 = 9422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15677) = 3 ^ 9 * m + 9422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15677.1, data_15_15677.2]

/-- Complete interval computation for depth 15, residue 15678. -/
theorem bounds_15_15678 : exactInterval 15 15678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15678 : oddCount 15678 15 = 11 ∧ acceleratedOrbit 15 15678 = 84770 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15678) = 3 ^ 11 * m + 84770 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15678.1, data_15_15678.2]

/-- Complete interval computation for depth 15, residue 15679. -/
theorem bounds_15_15679 : exactInterval 15 15679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15679 : oddCount 15679 15 = 11 ∧ acceleratedOrbit 15 15679 = 84770 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15679) = 3 ^ 11 * m + 84770 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15679.1, data_15_15679.2]

/-- Complete interval computation for depth 15, residue 15680. -/
theorem bounds_15_15680 : exactInterval 15 15680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15680 : oddCount 15680 15 = 4 ∧ acceleratedOrbit 15 15680 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15680) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15680.1, data_15_15680.2]

/-- Complete interval computation for depth 15, residue 15681. -/
theorem bounds_15_15681 : exactInterval 15 15681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15681 : oddCount 15681 15 = 7 ∧ acceleratedOrbit 15 15681 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15681) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15681.1, data_15_15681.2]

/-- Complete interval computation for depth 15, residue 15682. -/
theorem bounds_15_15682 : exactInterval 15 15682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15682 : oddCount 15682 15 = 6 ∧ acceleratedOrbit 15 15682 = 349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15682) = 3 ^ 6 * m + 349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15682.1, data_15_15682.2]

/-- Complete interval computation for depth 15, residue 15683. -/
theorem bounds_15_15683 : exactInterval 15 15683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15683 : oddCount 15683 15 = 6 ∧ acceleratedOrbit 15 15683 = 349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15683) = 3 ^ 6 * m + 349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15683.1, data_15_15683.2]

/-- Complete interval computation for depth 15, residue 15684. -/
theorem bounds_15_15684 : exactInterval 15 15684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15684 : oddCount 15684 15 = 7 ∧ acceleratedOrbit 15 15684 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15684) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15684.1, data_15_15684.2]

/-- Complete interval computation for depth 15, residue 15685. -/
theorem bounds_15_15685 : exactInterval 15 15685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15685 : oddCount 15685 15 = 7 ∧ acceleratedOrbit 15 15685 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15685) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15685.1, data_15_15685.2]

/-- Complete interval computation for depth 15, residue 15686. -/
theorem bounds_15_15686 : exactInterval 15 15686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15686 : oddCount 15686 15 = 7 ∧ acceleratedOrbit 15 15686 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15686) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15686.1, data_15_15686.2]

/-- Complete interval computation for depth 15, residue 15687. -/
theorem bounds_15_15687 : exactInterval 15 15687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15687 : oddCount 15687 15 = 9 ∧ acceleratedOrbit 15 15687 = 9424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15687) = 3 ^ 9 * m + 9424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15687.1, data_15_15687.2]

/-- Complete interval computation for depth 15, residue 15688. -/
theorem bounds_15_15688 : exactInterval 15 15688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15688 : oddCount 15688 15 = 10 ∧ acceleratedOrbit 15 15688 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15688) = 3 ^ 10 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15688.1, data_15_15688.2]

/-- Complete interval computation for depth 15, residue 15689. -/
theorem bounds_15_15689 : exactInterval 15 15689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15689 : oddCount 15689 15 = 8 ∧ acceleratedOrbit 15 15689 = 3142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15689) = 3 ^ 8 * m + 3142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15689.1, data_15_15689.2]

/-- Complete interval computation for depth 15, residue 15690. -/
theorem bounds_15_15690 : exactInterval 15 15690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15690 : oddCount 15690 15 = 10 ∧ acceleratedOrbit 15 15690 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15690) = 3 ^ 10 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15690.1, data_15_15690.2]

/-- Complete interval computation for depth 15, residue 15691. -/
theorem bounds_15_15691 : exactInterval 15 15691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15691 : oddCount 15691 15 = 7 ∧ acceleratedOrbit 15 15691 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15691) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15691.1, data_15_15691.2]

/-- Complete interval computation for depth 15, residue 15692. -/
theorem bounds_15_15692 : exactInterval 15 15692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15692 : oddCount 15692 15 = 10 ∧ acceleratedOrbit 15 15692 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15692) = 3 ^ 10 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15692.1, data_15_15692.2]

/-- Complete interval computation for depth 15, residue 15693. -/
theorem bounds_15_15693 : exactInterval 15 15693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15693 : oddCount 15693 15 = 10 ∧ acceleratedOrbit 15 15693 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15693) = 3 ^ 10 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15693.1, data_15_15693.2]

/-- Complete interval computation for depth 15, residue 15694. -/
theorem bounds_15_15694 : exactInterval 15 15694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15694 : oddCount 15694 15 = 8 ∧ acceleratedOrbit 15 15694 = 3143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15694) = 3 ^ 8 * m + 3143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15694.1, data_15_15694.2]

end Collatz.Research.PassageAtlas.Batch0479
