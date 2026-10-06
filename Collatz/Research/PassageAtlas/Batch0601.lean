import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0601

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19660. -/
theorem bounds_15_19660 : exactInterval 15 19660 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19660 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19660) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19660 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19660 : oddCount 19660 15 = 5 ∧ acceleratedOrbit 15 19660 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19660 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19660) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19660.1, data_15_19660.2]

/-- Complete interval computation for depth 15, residue 19661. -/
theorem bounds_15_19661 : exactInterval 15 19661 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19661 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19661) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19661 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19661 : oddCount 19661 15 = 5 ∧ acceleratedOrbit 15 19661 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19661 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19661) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19661.1, data_15_19661.2]

/-- Complete interval computation for depth 15, residue 19662. -/
theorem bounds_15_19662 : exactInterval 15 19662 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19662 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19662) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19662 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19662 : oddCount 19662 15 = 10 ∧ acceleratedOrbit 15 19662 = 35437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19662 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19662) = 3 ^ 10 * m + 35437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19662.1, data_15_19662.2]

/-- Complete interval computation for depth 15, residue 19663. -/
theorem bounds_15_19663 : exactInterval 15 19663 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19663 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19663) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19663 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19663 : oddCount 19663 15 = 10 ∧ acceleratedOrbit 15 19663 = 35437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19663 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19663) = 3 ^ 10 * m + 35437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19663.1, data_15_19663.2]

/-- Complete interval computation for depth 15, residue 19664. -/
theorem bounds_15_19664 : exactInterval 15 19664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19664 : oddCount 19664 15 = 4 ∧ acceleratedOrbit 15 19664 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19664) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19664.1, data_15_19664.2]

/-- Complete interval computation for depth 15, residue 19665. -/
theorem bounds_15_19665 : exactInterval 15 19665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19665 : oddCount 19665 15 = 9 ∧ acceleratedOrbit 15 19665 = 11816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19665) = 3 ^ 9 * m + 11816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19665.1, data_15_19665.2]

/-- Complete interval computation for depth 15, residue 19666. -/
theorem bounds_15_19666 : exactInterval 15 19666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19666 : oddCount 19666 15 = 9 ∧ acceleratedOrbit 15 19666 = 11816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19666) = 3 ^ 9 * m + 11816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19666.1, data_15_19666.2]

/-- Complete interval computation for depth 15, residue 19667. -/
theorem bounds_15_19667 : exactInterval 15 19667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19667 : oddCount 19667 15 = 9 ∧ acceleratedOrbit 15 19667 = 11816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19667) = 3 ^ 9 * m + 11816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19667.1, data_15_19667.2]

/-- Complete interval computation for depth 15, residue 19668. -/
theorem bounds_15_19668 : exactInterval 15 19668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19668 : oddCount 19668 15 = 4 ∧ acceleratedOrbit 15 19668 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19668) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19668.1, data_15_19668.2]

/-- Complete interval computation for depth 15, residue 19669. -/
theorem bounds_15_19669 : exactInterval 15 19669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19669 : oddCount 19669 15 = 4 ∧ acceleratedOrbit 15 19669 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19669) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19669.1, data_15_19669.2]

/-- Complete interval computation for depth 15, residue 19670. -/
theorem bounds_15_19670 : exactInterval 15 19670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19670 : oddCount 19670 15 = 9 ∧ acceleratedOrbit 15 19670 = 11819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19670) = 3 ^ 9 * m + 11819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19670.1, data_15_19670.2]

/-- Complete interval computation for depth 15, residue 19671. -/
theorem bounds_15_19671 : exactInterval 15 19671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19671 : oddCount 19671 15 = 9 ∧ acceleratedOrbit 15 19671 = 11819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19671) = 3 ^ 9 * m + 11819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19671.1, data_15_19671.2]

/-- Complete interval computation for depth 15, residue 19672. -/
theorem bounds_15_19672 : exactInterval 15 19672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19672 : oddCount 19672 15 = 9 ∧ acceleratedOrbit 15 19672 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19672) = 3 ^ 9 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19672.1, data_15_19672.2]

/-- Complete interval computation for depth 15, residue 19673. -/
theorem bounds_15_19673 : exactInterval 15 19673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19673 : oddCount 19673 15 = 9 ∧ acceleratedOrbit 15 19673 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19673) = 3 ^ 9 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19673.1, data_15_19673.2]

/-- Complete interval computation for depth 15, residue 19674. -/
theorem bounds_15_19674 : exactInterval 15 19674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19674 : oddCount 19674 15 = 9 ∧ acceleratedOrbit 15 19674 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19674) = 3 ^ 9 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19674.1, data_15_19674.2]

/-- Complete interval computation for depth 15, residue 19675. -/
theorem bounds_15_19675 : exactInterval 15 19675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19675 : oddCount 19675 15 = 8 ∧ acceleratedOrbit 15 19675 = 3941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19675) = 3 ^ 8 * m + 3941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19675.1, data_15_19675.2]

/-- Complete interval computation for depth 15, residue 19676. -/
theorem bounds_15_19676 : exactInterval 15 19676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19676 : oddCount 19676 15 = 9 ∧ acceleratedOrbit 15 19676 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19676) = 3 ^ 9 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19676.1, data_15_19676.2]

/-- Complete interval computation for depth 15, residue 19677. -/
theorem bounds_15_19677 : exactInterval 15 19677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19677 : oddCount 19677 15 = 9 ∧ acceleratedOrbit 15 19677 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19677) = 3 ^ 9 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19677.1, data_15_19677.2]

/-- Complete interval computation for depth 15, residue 19678. -/
theorem bounds_15_19678 : exactInterval 15 19678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19678 : oddCount 19678 15 = 8 ∧ acceleratedOrbit 15 19678 = 3941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19678) = 3 ^ 8 * m + 3941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19678.1, data_15_19678.2]

/-- Complete interval computation for depth 15, residue 19679. -/
theorem bounds_15_19679 : exactInterval 15 19679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19679 : oddCount 19679 15 = 8 ∧ acceleratedOrbit 15 19679 = 3941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19679) = 3 ^ 8 * m + 3941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19679.1, data_15_19679.2]

/-- Complete interval computation for depth 15, residue 19680. -/
theorem bounds_15_19680 : exactInterval 15 19680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19680 : oddCount 19680 15 = 7 ∧ acceleratedOrbit 15 19680 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19680) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19680.1, data_15_19680.2]

/-- Complete interval computation for depth 15, residue 19681. -/
theorem bounds_15_19681 : exactInterval 15 19681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19681 : oddCount 19681 15 = 10 ∧ acceleratedOrbit 15 19681 = 35471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19681) = 3 ^ 10 * m + 35471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19681.1, data_15_19681.2]

/-- Complete interval computation for depth 15, residue 19682. -/
theorem bounds_15_19682 : exactInterval 15 19682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19682 : oddCount 19682 15 = 4 ∧ acceleratedOrbit 15 19682 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19682) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19682.1, data_15_19682.2]

/-- Complete interval computation for depth 15, residue 19683. -/
theorem bounds_15_19683 : exactInterval 15 19683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19683 : oddCount 19683 15 = 4 ∧ acceleratedOrbit 15 19683 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19683) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19683.1, data_15_19683.2]

/-- Complete interval computation for depth 15, residue 19684. -/
theorem bounds_15_19684 : exactInterval 15 19684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19684 : oddCount 19684 15 = 8 ∧ acceleratedOrbit 15 19684 = 3944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19684) = 3 ^ 8 * m + 3944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19684.1, data_15_19684.2]

/-- Complete interval computation for depth 15, residue 19685. -/
theorem bounds_15_19685 : exactInterval 15 19685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19685 : oddCount 19685 15 = 8 ∧ acceleratedOrbit 15 19685 = 3944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19685) = 3 ^ 8 * m + 3944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19685.1, data_15_19685.2]

/-- Complete interval computation for depth 15, residue 19686. -/
theorem bounds_15_19686 : exactInterval 15 19686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19686 : oddCount 19686 15 = 8 ∧ acceleratedOrbit 15 19686 = 3944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19686) = 3 ^ 8 * m + 3944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19686.1, data_15_19686.2]

/-- Complete interval computation for depth 15, residue 19687. -/
theorem bounds_15_19687 : exactInterval 15 19687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19687 : oddCount 19687 15 = 10 ∧ acceleratedOrbit 15 19687 = 35480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19687) = 3 ^ 10 * m + 35480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19687.1, data_15_19687.2]

/-- Complete interval computation for depth 15, residue 19688. -/
theorem bounds_15_19688 : exactInterval 15 19688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19688 : oddCount 19688 15 = 7 ∧ acceleratedOrbit 15 19688 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19688) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19688.1, data_15_19688.2]

/-- Complete interval computation for depth 15, residue 19689. -/
theorem bounds_15_19689 : exactInterval 15 19689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19689 : oddCount 19689 15 = 8 ∧ acceleratedOrbit 15 19689 = 3943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19689) = 3 ^ 8 * m + 3943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19689.1, data_15_19689.2]

/-- Complete interval computation for depth 15, residue 19690. -/
theorem bounds_15_19690 : exactInterval 15 19690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19690 : oddCount 19690 15 = 7 ∧ acceleratedOrbit 15 19690 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19690) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19690.1, data_15_19690.2]

/-- Complete interval computation for depth 15, residue 19691. -/
theorem bounds_15_19691 : exactInterval 15 19691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19691 : oddCount 19691 15 = 10 ∧ acceleratedOrbit 15 19691 = 35488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19691) = 3 ^ 10 * m + 35488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19691.1, data_15_19691.2]

/-- Complete interval computation for depth 15, residue 19692. -/
theorem bounds_15_19692 : exactInterval 15 19692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19692 : oddCount 19692 15 = 7 ∧ acceleratedOrbit 15 19692 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19692) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19692.1, data_15_19692.2]

end Collatz.Research.PassageAtlas.Batch0601
