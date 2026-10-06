import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0382

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2780. -/
theorem bounds_12_2780 : exactInterval 12 2780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2780 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2780) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2780 : oddCount 2780 12 = 6 ∧ acceleratedOrbit 12 2780 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2780 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2780) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2780.1, data_12_2780.2]

/-- Complete interval computation for depth 12, residue 2781. -/
theorem bounds_12_2781 : exactInterval 12 2781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2781 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2781) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2781 : oddCount 2781 12 = 6 ∧ acceleratedOrbit 12 2781 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2781 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2781) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2781.1, data_12_2781.2]

/-- Complete interval computation for depth 12, residue 2782. -/
theorem bounds_12_2782 : exactInterval 12 2782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2782 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2782) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2782 : oddCount 2782 12 = 7 ∧ acceleratedOrbit 12 2782 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2782 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2782) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2782.1, data_12_2782.2]

/-- Complete interval computation for depth 12, residue 2783. -/
theorem bounds_12_2783 : exactInterval 12 2783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2783 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2783) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2783 : oddCount 2783 12 = 7 ∧ acceleratedOrbit 12 2783 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2783 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2783) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2783.1, data_12_2783.2]

/-- Complete interval computation for depth 12, residue 2784. -/
theorem bounds_12_2784 : exactInterval 12 2784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2784 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2784) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2784 : oddCount 2784 12 = 4 ∧ acceleratedOrbit 12 2784 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2784 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2784) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2784.1, data_12_2784.2]

/-- Complete interval computation for depth 12, residue 2785. -/
theorem bounds_12_2785 : exactInterval 12 2785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2785 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2785) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2785 : oddCount 2785 12 = 8 ∧ acceleratedOrbit 12 2785 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2785 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2785) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2785.1, data_12_2785.2]

/-- Complete interval computation for depth 12, residue 2786. -/
theorem bounds_12_2786 : exactInterval 12 2786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2786 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2786) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2786 : oddCount 2786 12 = 4 ∧ acceleratedOrbit 12 2786 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2786 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2786) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2786.1, data_12_2786.2]

/-- Complete interval computation for depth 12, residue 2787. -/
theorem bounds_12_2787 : exactInterval 12 2787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2787 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2787) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2787 : oddCount 2787 12 = 4 ∧ acceleratedOrbit 12 2787 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2787 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2787) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2787.1, data_12_2787.2]

/-- Complete interval computation for depth 12, residue 2788. -/
theorem bounds_12_2788 : exactInterval 12 2788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2788 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2788) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2788 : oddCount 2788 12 = 5 ∧ acceleratedOrbit 12 2788 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2788 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2788) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2788.1, data_12_2788.2]

/-- Complete interval computation for depth 12, residue 2789. -/
theorem bounds_12_2789 : exactInterval 12 2789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2789 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2789) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2789 : oddCount 2789 12 = 5 ∧ acceleratedOrbit 12 2789 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2789 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2789) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2789.1, data_12_2789.2]

/-- Complete interval computation for depth 12, residue 2790. -/
theorem bounds_12_2790 : exactInterval 12 2790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2790 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2790) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2790 : oddCount 2790 12 = 5 ∧ acceleratedOrbit 12 2790 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2790 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2790) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2790.1, data_12_2790.2]

/-- Complete interval computation for depth 12, residue 2791. -/
theorem bounds_12_2791 : exactInterval 12 2791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2791 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2791) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2791 : oddCount 2791 12 = 10 ∧ acceleratedOrbit 12 2791 = 40256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2791 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2791) = 3 ^ 10 * m + 40256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2791.1, data_12_2791.2]

/-- Complete interval computation for depth 12, residue 2792. -/
theorem bounds_12_2792 : exactInterval 12 2792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2792 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2792) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2792 : oddCount 2792 12 = 4 ∧ acceleratedOrbit 12 2792 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2792 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2792) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2792.1, data_12_2792.2]

/-- Complete interval computation for depth 12, residue 2793. -/
theorem bounds_12_2793 : exactInterval 12 2793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2793 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2793) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2793 : oddCount 2793 12 = 8 ∧ acceleratedOrbit 12 2793 = 4477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2793 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2793) = 3 ^ 8 * m + 4477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2793.1, data_12_2793.2]

/-- Complete interval computation for depth 12, residue 2794. -/
theorem bounds_12_2794 : exactInterval 12 2794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2794 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2794) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2794 : oddCount 2794 12 = 4 ∧ acceleratedOrbit 12 2794 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2794 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2794) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2794.1, data_12_2794.2]

end Collatz.Research.StoppingAtlas.Batch0382
