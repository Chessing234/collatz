import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0418

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13664. -/
theorem bounds_15_13664 : exactInterval 15 13664 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13664 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13664) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13664 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13664 : oddCount 13664 15 = 7 ∧ acceleratedOrbit 15 13664 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13664 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13664) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13664.1, data_15_13664.2]

/-- Complete interval computation for depth 15, residue 13665. -/
theorem bounds_15_13665 : exactInterval 15 13665 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13665 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13665) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13665 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13665 : oddCount 13665 15 = 8 ∧ acceleratedOrbit 15 13665 = 2737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13665 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13665) = 3 ^ 8 * m + 2737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13665.1, data_15_13665.2]

/-- Complete interval computation for depth 15, residue 13666. -/
theorem bounds_15_13666 : exactInterval 15 13666 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13666 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13666) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13666 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13666 : oddCount 13666 15 = 6 ∧ acceleratedOrbit 15 13666 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13666 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13666) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13666.1, data_15_13666.2]

/-- Complete interval computation for depth 15, residue 13667. -/
theorem bounds_15_13667 : exactInterval 15 13667 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13667 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13667) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13667 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13667 : oddCount 13667 15 = 6 ∧ acceleratedOrbit 15 13667 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13667 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13667) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13667.1, data_15_13667.2]

/-- Complete interval computation for depth 15, residue 13668. -/
theorem bounds_15_13668 : exactInterval 15 13668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13668 : oddCount 13668 15 = 6 ∧ acceleratedOrbit 15 13668 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13668) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13668.1, data_15_13668.2]

/-- Complete interval computation for depth 15, residue 13669. -/
theorem bounds_15_13669 : exactInterval 15 13669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13669 : oddCount 13669 15 = 6 ∧ acceleratedOrbit 15 13669 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13669) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13669.1, data_15_13669.2]

/-- Complete interval computation for depth 15, residue 13670. -/
theorem bounds_15_13670 : exactInterval 15 13670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13670 : oddCount 13670 15 = 6 ∧ acceleratedOrbit 15 13670 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13670) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13670.1, data_15_13670.2]

/-- Complete interval computation for depth 15, residue 13671. -/
theorem bounds_15_13671 : exactInterval 15 13671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13671 : oddCount 13671 15 = 10 ∧ acceleratedOrbit 15 13671 = 24638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13671) = 3 ^ 10 * m + 24638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13671.1, data_15_13671.2]

/-- Complete interval computation for depth 15, residue 13672. -/
theorem bounds_15_13672 : exactInterval 15 13672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13672 : oddCount 13672 15 = 7 ∧ acceleratedOrbit 15 13672 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13672) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13672.1, data_15_13672.2]

/-- Complete interval computation for depth 15, residue 13673. -/
theorem bounds_15_13673 : exactInterval 15 13673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13673 : oddCount 13673 15 = 7 ∧ acceleratedOrbit 15 13673 = 913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13673) = 3 ^ 7 * m + 913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13673.1, data_15_13673.2]

/-- Complete interval computation for depth 15, residue 13674. -/
theorem bounds_15_13674 : exactInterval 15 13674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13674 : oddCount 13674 15 = 7 ∧ acceleratedOrbit 15 13674 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13674) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13674.1, data_15_13674.2]

/-- Complete interval computation for depth 15, residue 13675. -/
theorem bounds_15_13675 : exactInterval 15 13675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13675 : oddCount 13675 15 = 10 ∧ acceleratedOrbit 15 13675 = 24650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13675) = 3 ^ 10 * m + 24650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13675.1, data_15_13675.2]

/-- Complete interval computation for depth 15, residue 13676. -/
theorem bounds_15_13676 : exactInterval 15 13676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13676 : oddCount 13676 15 = 8 ∧ acceleratedOrbit 15 13676 = 2740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13676) = 3 ^ 8 * m + 2740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13676.1, data_15_13676.2]

/-- Complete interval computation for depth 15, residue 13677. -/
theorem bounds_15_13677 : exactInterval 15 13677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13677 : oddCount 13677 15 = 8 ∧ acceleratedOrbit 15 13677 = 2740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13677) = 3 ^ 8 * m + 2740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13677.1, data_15_13677.2]

/-- Complete interval computation for depth 15, residue 13678. -/
theorem bounds_15_13678 : exactInterval 15 13678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13678 : oddCount 13678 15 = 8 ∧ acceleratedOrbit 15 13678 = 2740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13678) = 3 ^ 8 * m + 2740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13678.1, data_15_13678.2]

/-- Complete interval computation for depth 15, residue 13679. -/
theorem bounds_15_13679 : exactInterval 15 13679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13679 : oddCount 13679 15 = 9 ∧ acceleratedOrbit 15 13679 = 8218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13679) = 3 ^ 9 * m + 8218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13679.1, data_15_13679.2]

/-- Complete interval computation for depth 15, residue 13680. -/
theorem bounds_15_13680 : exactInterval 15 13680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13680 : oddCount 13680 15 = 7 ∧ acceleratedOrbit 15 13680 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13680) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13680.1, data_15_13680.2]

/-- Complete interval computation for depth 15, residue 13681. -/
theorem bounds_15_13681 : exactInterval 15 13681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13681 : oddCount 13681 15 = 7 ∧ acceleratedOrbit 15 13681 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13681) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13681.1, data_15_13681.2]

/-- Complete interval computation for depth 15, residue 13682. -/
theorem bounds_15_13682 : exactInterval 15 13682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13682 : oddCount 13682 15 = 6 ∧ acceleratedOrbit 15 13682 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13682) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13682.1, data_15_13682.2]

/-- Complete interval computation for depth 15, residue 13683. -/
theorem bounds_15_13683 : exactInterval 15 13683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13683 : oddCount 13683 15 = 6 ∧ acceleratedOrbit 15 13683 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13683) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13683.1, data_15_13683.2]

/-- Complete interval computation for depth 15, residue 13684. -/
theorem bounds_15_13684 : exactInterval 15 13684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13684 : oddCount 13684 15 = 7 ∧ acceleratedOrbit 15 13684 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13684) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13684.1, data_15_13684.2]

/-- Complete interval computation for depth 15, residue 13685. -/
theorem bounds_15_13685 : exactInterval 15 13685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13685 : oddCount 13685 15 = 7 ∧ acceleratedOrbit 15 13685 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13685) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13685.1, data_15_13685.2]

/-- Complete interval computation for depth 15, residue 13686. -/
theorem bounds_15_13686 : exactInterval 15 13686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13686 : oddCount 13686 15 = 9 ∧ acceleratedOrbit 15 13686 = 8225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13686) = 3 ^ 9 * m + 8225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13686.1, data_15_13686.2]

/-- Complete interval computation for depth 15, residue 13687. -/
theorem bounds_15_13687 : exactInterval 15 13687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13687 : oddCount 13687 15 = 9 ∧ acceleratedOrbit 15 13687 = 8225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13687) = 3 ^ 9 * m + 8225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13687.1, data_15_13687.2]

/-- Complete interval computation for depth 15, residue 13688. -/
theorem bounds_15_13688 : exactInterval 15 13688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13688 : oddCount 13688 15 = 8 ∧ acceleratedOrbit 15 13688 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13688) = 3 ^ 8 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13688.1, data_15_13688.2]

/-- Complete interval computation for depth 15, residue 13689. -/
theorem bounds_15_13689 : exactInterval 15 13689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13689 : oddCount 13689 15 = 9 ∧ acceleratedOrbit 15 13689 = 8224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13689) = 3 ^ 9 * m + 8224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13689.1, data_15_13689.2]

/-- Complete interval computation for depth 15, residue 13690. -/
theorem bounds_15_13690 : exactInterval 15 13690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13690 : oddCount 13690 15 = 8 ∧ acceleratedOrbit 15 13690 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13690) = 3 ^ 8 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13690.1, data_15_13690.2]

/-- Complete interval computation for depth 15, residue 13691. -/
theorem bounds_15_13691 : exactInterval 15 13691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13691 : oddCount 13691 15 = 7 ∧ acceleratedOrbit 15 13691 = 914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13691) = 3 ^ 7 * m + 914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13691.1, data_15_13691.2]

/-- Complete interval computation for depth 15, residue 13692. -/
theorem bounds_15_13692 : exactInterval 15 13692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13692 : oddCount 13692 15 = 8 ∧ acceleratedOrbit 15 13692 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13692) = 3 ^ 8 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13692.1, data_15_13692.2]

/-- Complete interval computation for depth 15, residue 13693. -/
theorem bounds_15_13693 : exactInterval 15 13693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13693 : oddCount 13693 15 = 8 ∧ acceleratedOrbit 15 13693 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13693) = 3 ^ 8 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13693.1, data_15_13693.2]

/-- Complete interval computation for depth 15, residue 13694. -/
theorem bounds_15_13694 : exactInterval 15 13694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13694 : oddCount 13694 15 = 9 ∧ acceleratedOrbit 15 13694 = 8227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13694) = 3 ^ 9 * m + 8227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13694.1, data_15_13694.2]

/-- Complete interval computation for depth 15, residue 13695. -/
theorem bounds_15_13695 : exactInterval 15 13695 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13695) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13695 : oddCount 13695 15 = 9 ∧ acceleratedOrbit 15 13695 = 8227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13695) = 3 ^ 9 * m + 8227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13695.1, data_15_13695.2]

/-- Complete interval computation for depth 15, residue 13696. -/
theorem bounds_15_13696 : exactInterval 15 13696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13696 : oddCount 13696 15 = 5 ∧ acceleratedOrbit 15 13696 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13696) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13696.1, data_15_13696.2]

end Collatz.Research.PassageAtlas.Batch0418
