import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0837

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5672. -/
theorem bounds_13_5672 : exactInterval 13 5672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5672 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5672) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5672 : oddCount 5672 13 = 3 ∧ acceleratedOrbit 13 5672 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5672 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5672) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5672.1, data_13_5672.2]

/-- Complete interval computation for depth 13, residue 5673. -/
theorem bounds_13_5673 : exactInterval 13 5673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5673 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5673) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5673 : oddCount 5673 13 = 11 ∧ acceleratedOrbit 13 5673 = 122714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5673 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5673) = 3 ^ 11 * m + 122714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5673.1, data_13_5673.2]

/-- Complete interval computation for depth 13, residue 5674. -/
theorem bounds_13_5674 : exactInterval 13 5674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5674 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5674) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5674 : oddCount 5674 13 = 3 ∧ acceleratedOrbit 13 5674 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5674 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5674) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5674.1, data_13_5674.2]

/-- Complete interval computation for depth 13, residue 5675. -/
theorem bounds_13_5675 : exactInterval 13 5675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5675 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5675) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5675 : oddCount 5675 13 = 6 ∧ acceleratedOrbit 13 5675 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5675 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5675) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5675.1, data_13_5675.2]

/-- Complete interval computation for depth 13, residue 5676. -/
theorem bounds_13_5676 : exactInterval 13 5676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5676 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5676) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5676 : oddCount 5676 13 = 6 ∧ acceleratedOrbit 13 5676 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5676 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5676) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5676.1, data_13_5676.2]

/-- Complete interval computation for depth 13, residue 5677. -/
theorem bounds_13_5677 : exactInterval 13 5677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5677 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5677) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5677 : oddCount 5677 13 = 6 ∧ acceleratedOrbit 13 5677 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5677 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5677) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5677.1, data_13_5677.2]

/-- Complete interval computation for depth 13, residue 5678. -/
theorem bounds_13_5678 : exactInterval 13 5678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5678 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5678) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5678 : oddCount 5678 13 = 6 ∧ acceleratedOrbit 13 5678 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5678 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5678) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5678.1, data_13_5678.2]

/-- Complete interval computation for depth 13, residue 5679. -/
theorem bounds_13_5679 : exactInterval 13 5679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5679 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5679) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5679 : oddCount 5679 13 = 10 ∧ acceleratedOrbit 13 5679 = 40945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5679 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5679) = 3 ^ 10 * m + 40945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5679.1, data_13_5679.2]

/-- Complete interval computation for depth 13, residue 5680. -/
theorem bounds_13_5680 : exactInterval 13 5680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5680 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5680) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5680 : oddCount 5680 13 = 3 ∧ acceleratedOrbit 13 5680 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5680 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5680) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5680.1, data_13_5680.2]

/-- Complete interval computation for depth 13, residue 5681. -/
theorem bounds_13_5681 : exactInterval 13 5681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5681 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5681) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5681 : oddCount 5681 13 = 8 ∧ acceleratedOrbit 13 5681 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5681 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5681) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5681.1, data_13_5681.2]

/-- Complete interval computation for depth 13, residue 5682. -/
theorem bounds_13_5682 : exactInterval 13 5682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5682 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5682) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5682 : oddCount 5682 13 = 8 ∧ acceleratedOrbit 13 5682 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5682 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5682) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5682.1, data_13_5682.2]

/-- Complete interval computation for depth 13, residue 5683. -/
theorem bounds_13_5683 : exactInterval 13 5683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5683 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5683) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5683 : oddCount 5683 13 = 8 ∧ acceleratedOrbit 13 5683 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5683 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5683) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5683.1, data_13_5683.2]

/-- Complete interval computation for depth 13, residue 5684. -/
theorem bounds_13_5684 : exactInterval 13 5684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5684 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5684) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5684 : oddCount 5684 13 = 3 ∧ acceleratedOrbit 13 5684 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5684 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5684) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5684.1, data_13_5684.2]

/-- Complete interval computation for depth 13, residue 5685. -/
theorem bounds_13_5685 : exactInterval 13 5685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5685 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5685) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5685 : oddCount 5685 13 = 3 ∧ acceleratedOrbit 13 5685 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5685 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5685) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5685.1, data_13_5685.2]

/-- Complete interval computation for depth 13, residue 5686. -/
theorem bounds_13_5686 : exactInterval 13 5686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5686 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5686) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5686 : oddCount 5686 13 = 10 ∧ acceleratedOrbit 13 5686 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5686 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5686) = 3 ^ 10 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5686.1, data_13_5686.2]

/-- Complete interval computation for depth 13, residue 5687. -/
theorem bounds_13_5687 : exactInterval 13 5687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5687 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5687) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5687 : oddCount 5687 13 = 10 ∧ acceleratedOrbit 13 5687 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5687 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5687) = 3 ^ 10 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5687.1, data_13_5687.2]

end Collatz.Research.StoppingAtlas.Batch0837
