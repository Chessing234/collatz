import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0174

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5668. -/
theorem bounds_15_5668 : exactInterval 15 5668 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5668 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5668) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5668 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5668 : oddCount 5668 15 = 7 ∧ acceleratedOrbit 15 5668 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5668 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5668) = 3 ^ 7 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5668.1, data_15_5668.2]

/-- Complete interval computation for depth 15, residue 5669. -/
theorem bounds_15_5669 : exactInterval 15 5669 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5669 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5669) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5669 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5669 : oddCount 5669 15 = 7 ∧ acceleratedOrbit 15 5669 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5669 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5669) = 3 ^ 7 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5669.1, data_15_5669.2]

/-- Complete interval computation for depth 15, residue 5670. -/
theorem bounds_15_5670 : exactInterval 15 5670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5670 : oddCount 5670 15 = 7 ∧ acceleratedOrbit 15 5670 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5670) = 3 ^ 7 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5670.1, data_15_5670.2]

/-- Complete interval computation for depth 15, residue 5671. -/
theorem bounds_15_5671 : exactInterval 15 5671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5671 : oddCount 5671 15 = 7 ∧ acceleratedOrbit 15 5671 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5671) = 3 ^ 7 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5671.1, data_15_5671.2]

/-- Complete interval computation for depth 15, residue 5672. -/
theorem bounds_15_5672 : exactInterval 15 5672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5672 : oddCount 5672 15 = 5 ∧ acceleratedOrbit 15 5672 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5672) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5672.1, data_15_5672.2]

/-- Complete interval computation for depth 15, residue 5673. -/
theorem bounds_15_5673 : exactInterval 15 5673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5673 : oddCount 5673 15 = 12 ∧ acceleratedOrbit 15 5673 = 92036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5673) = 3 ^ 12 * m + 92036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5673.1, data_15_5673.2]

/-- Complete interval computation for depth 15, residue 5674. -/
theorem bounds_15_5674 : exactInterval 15 5674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5674 : oddCount 5674 15 = 5 ∧ acceleratedOrbit 15 5674 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5674) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5674.1, data_15_5674.2]

/-- Complete interval computation for depth 15, residue 5675. -/
theorem bounds_15_5675 : exactInterval 15 5675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5675 : oddCount 5675 15 = 7 ∧ acceleratedOrbit 15 5675 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5675) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5675.1, data_15_5675.2]

/-- Complete interval computation for depth 15, residue 5676. -/
theorem bounds_15_5676 : exactInterval 15 5676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5676 : oddCount 5676 15 = 7 ∧ acceleratedOrbit 15 5676 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5676) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5676.1, data_15_5676.2]

/-- Complete interval computation for depth 15, residue 5677. -/
theorem bounds_15_5677 : exactInterval 15 5677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5677 : oddCount 5677 15 = 7 ∧ acceleratedOrbit 15 5677 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5677) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5677.1, data_15_5677.2]

/-- Complete interval computation for depth 15, residue 5678. -/
theorem bounds_15_5678 : exactInterval 15 5678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5678 : oddCount 5678 15 = 7 ∧ acceleratedOrbit 15 5678 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5678) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5678.1, data_15_5678.2]

/-- Complete interval computation for depth 15, residue 5679. -/
theorem bounds_15_5679 : exactInterval 15 5679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5679 : oddCount 5679 15 = 11 ∧ acceleratedOrbit 15 5679 = 30709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5679) = 3 ^ 11 * m + 30709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5679.1, data_15_5679.2]

/-- Complete interval computation for depth 15, residue 5680. -/
theorem bounds_15_5680 : exactInterval 15 5680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5680 : oddCount 5680 15 = 5 ∧ acceleratedOrbit 15 5680 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5680) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5680.1, data_15_5680.2]

/-- Complete interval computation for depth 15, residue 5681. -/
theorem bounds_15_5681 : exactInterval 15 5681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5681 : oddCount 5681 15 = 8 ∧ acceleratedOrbit 15 5681 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5681) = 3 ^ 8 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5681.1, data_15_5681.2]

/-- Complete interval computation for depth 15, residue 5682. -/
theorem bounds_15_5682 : exactInterval 15 5682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5682 : oddCount 5682 15 = 8 ∧ acceleratedOrbit 15 5682 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5682) = 3 ^ 8 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5682.1, data_15_5682.2]

/-- Complete interval computation for depth 15, residue 5683. -/
theorem bounds_15_5683 : exactInterval 15 5683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5683 : oddCount 5683 15 = 8 ∧ acceleratedOrbit 15 5683 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5683) = 3 ^ 8 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5683.1, data_15_5683.2]

/-- Complete interval computation for depth 15, residue 5684. -/
theorem bounds_15_5684 : exactInterval 15 5684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5684 : oddCount 5684 15 = 5 ∧ acceleratedOrbit 15 5684 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5684) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5684.1, data_15_5684.2]

/-- Complete interval computation for depth 15, residue 5685. -/
theorem bounds_15_5685 : exactInterval 15 5685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5685 : oddCount 5685 15 = 5 ∧ acceleratedOrbit 15 5685 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5685) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5685.1, data_15_5685.2]

/-- Complete interval computation for depth 15, residue 5686. -/
theorem bounds_15_5686 : exactInterval 15 5686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5686 : oddCount 5686 15 = 11 ∧ acceleratedOrbit 15 5686 = 30755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5686) = 3 ^ 11 * m + 30755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5686.1, data_15_5686.2]

/-- Complete interval computation for depth 15, residue 5687. -/
theorem bounds_15_5687 : exactInterval 15 5687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5687 : oddCount 5687 15 = 11 ∧ acceleratedOrbit 15 5687 = 30755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5687) = 3 ^ 11 * m + 30755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5687.1, data_15_5687.2]

/-- Complete interval computation for depth 15, residue 5688. -/
theorem bounds_15_5688 : exactInterval 15 5688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5688 : oddCount 5688 15 = 6 ∧ acceleratedOrbit 15 5688 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5688) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5688.1, data_15_5688.2]

/-- Complete interval computation for depth 15, residue 5689. -/
theorem bounds_15_5689 : exactInterval 15 5689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5689 : oddCount 5689 15 = 7 ∧ acceleratedOrbit 15 5689 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5689) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5689.1, data_15_5689.2]

/-- Complete interval computation for depth 15, residue 5690. -/
theorem bounds_15_5690 : exactInterval 15 5690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5690 : oddCount 5690 15 = 6 ∧ acceleratedOrbit 15 5690 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5690) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5690.1, data_15_5690.2]

/-- Complete interval computation for depth 15, residue 5691. -/
theorem bounds_15_5691 : exactInterval 15 5691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5691 : oddCount 5691 15 = 9 ∧ acceleratedOrbit 15 5691 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5691) = 3 ^ 9 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5691.1, data_15_5691.2]

/-- Complete interval computation for depth 15, residue 5692. -/
theorem bounds_15_5692 : exactInterval 15 5692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5692 : oddCount 5692 15 = 6 ∧ acceleratedOrbit 15 5692 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5692) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5692.1, data_15_5692.2]

/-- Complete interval computation for depth 15, residue 5693. -/
theorem bounds_15_5693 : exactInterval 15 5693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5693 : oddCount 5693 15 = 6 ∧ acceleratedOrbit 15 5693 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5693) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5693.1, data_15_5693.2]

/-- Complete interval computation for depth 15, residue 5694. -/
theorem bounds_15_5694 : exactInterval 15 5694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5694 : oddCount 5694 15 = 9 ∧ acceleratedOrbit 15 5694 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5694) = 3 ^ 9 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5694.1, data_15_5694.2]

/-- Complete interval computation for depth 15, residue 5695. -/
theorem bounds_15_5695 : exactInterval 15 5695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5695 : oddCount 5695 15 = 9 ∧ acceleratedOrbit 15 5695 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5695) = 3 ^ 9 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5695.1, data_15_5695.2]

/-- Complete interval computation for depth 15, residue 5696. -/
theorem bounds_15_5696 : exactInterval 15 5696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5696 : oddCount 5696 15 = 5 ∧ acceleratedOrbit 15 5696 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5696) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5696.1, data_15_5696.2]

/-- Complete interval computation for depth 15, residue 5697. -/
theorem bounds_15_5697 : exactInterval 15 5697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5697 : oddCount 5697 15 = 6 ∧ acceleratedOrbit 15 5697 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5697) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5697.1, data_15_5697.2]

/-- Complete interval computation for depth 15, residue 5698. -/
theorem bounds_15_5698 : exactInterval 15 5698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5698 : oddCount 5698 15 = 6 ∧ acceleratedOrbit 15 5698 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5698) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5698.1, data_15_5698.2]

/-- Complete interval computation for depth 15, residue 5699. -/
theorem bounds_15_5699 : exactInterval 15 5699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5699 : oddCount 5699 15 = 6 ∧ acceleratedOrbit 15 5699 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5699) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5699.1, data_15_5699.2]

/-- Complete interval computation for depth 15, residue 5700. -/
theorem bounds_15_5700 : exactInterval 15 5700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5700 : oddCount 5700 15 = 6 ∧ acceleratedOrbit 15 5700 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5700) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5700.1, data_15_5700.2]

end Collatz.Research.PassageAtlas.Batch0174
