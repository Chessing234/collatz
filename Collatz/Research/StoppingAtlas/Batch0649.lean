import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0649

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2785. -/
theorem bounds_13_2785 : exactInterval 13 2785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2785 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2785) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2785 : oddCount 2785 13 = 9 ∧ acceleratedOrbit 13 2785 = 6698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2785 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2785) = 3 ^ 9 * m + 6698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2785.1, data_13_2785.2]

/-- Complete interval computation for depth 13, residue 2786. -/
theorem bounds_13_2786 : exactInterval 13 2786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2786 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2786) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2786 : oddCount 2786 13 = 4 ∧ acceleratedOrbit 13 2786 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2786 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2786) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2786.1, data_13_2786.2]

/-- Complete interval computation for depth 13, residue 2787. -/
theorem bounds_13_2787 : exactInterval 13 2787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2787 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2787) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2787 : oddCount 2787 13 = 4 ∧ acceleratedOrbit 13 2787 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2787 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2787) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2787.1, data_13_2787.2]

/-- Complete interval computation for depth 13, residue 2788. -/
theorem bounds_13_2788 : exactInterval 13 2788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2788 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2788) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2788 : oddCount 2788 13 = 5 ∧ acceleratedOrbit 13 2788 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2788 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2788) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2788.1, data_13_2788.2]

/-- Complete interval computation for depth 13, residue 2789. -/
theorem bounds_13_2789 : exactInterval 13 2789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2789 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2789) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2789 : oddCount 2789 13 = 5 ∧ acceleratedOrbit 13 2789 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2789 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2789) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2789.1, data_13_2789.2]

/-- Complete interval computation for depth 13, residue 2790. -/
theorem bounds_13_2790 : exactInterval 13 2790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2790 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2790) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2790 : oddCount 2790 13 = 5 ∧ acceleratedOrbit 13 2790 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2790 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2790) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2790.1, data_13_2790.2]

/-- Complete interval computation for depth 13, residue 2791. -/
theorem bounds_13_2791 : exactInterval 13 2791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2791 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2791) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2791 : oddCount 2791 13 = 10 ∧ acceleratedOrbit 13 2791 = 20128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2791 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2791) = 3 ^ 10 * m + 20128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2791.1, data_13_2791.2]

/-- Complete interval computation for depth 13, residue 2792. -/
theorem bounds_13_2792 : exactInterval 13 2792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2792 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2792) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2792 : oddCount 2792 13 = 4 ∧ acceleratedOrbit 13 2792 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2792 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2792) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2792.1, data_13_2792.2]

/-- Complete interval computation for depth 13, residue 2793. -/
theorem bounds_13_2793 : exactInterval 13 2793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2793 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2793) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2793 : oddCount 2793 13 = 9 ∧ acceleratedOrbit 13 2793 = 6716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2793 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2793) = 3 ^ 9 * m + 6716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2793.1, data_13_2793.2]

/-- Complete interval computation for depth 13, residue 2794. -/
theorem bounds_13_2794 : exactInterval 13 2794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2794 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2794) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2794 : oddCount 2794 13 = 4 ∧ acceleratedOrbit 13 2794 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2794 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2794) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2794.1, data_13_2794.2]

/-- Complete interval computation for depth 13, residue 2795. -/
theorem bounds_13_2795 : exactInterval 13 2795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2795 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2795) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2795 : oddCount 2795 13 = 9 ∧ acceleratedOrbit 13 2795 = 6722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2795 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2795) = 3 ^ 9 * m + 6722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2795.1, data_13_2795.2]

/-- Complete interval computation for depth 13, residue 2796. -/
theorem bounds_13_2796 : exactInterval 13 2796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2796 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2796) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2796 : oddCount 2796 13 = 7 ∧ acceleratedOrbit 13 2796 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2796 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2796) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2796.1, data_13_2796.2]

/-- Complete interval computation for depth 13, residue 2797. -/
theorem bounds_13_2797 : exactInterval 13 2797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2797 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2797) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2797 : oddCount 2797 13 = 7 ∧ acceleratedOrbit 13 2797 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2797 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2797) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2797.1, data_13_2797.2]

/-- Complete interval computation for depth 13, residue 2798. -/
theorem bounds_13_2798 : exactInterval 13 2798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2798 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2798) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2798 : oddCount 2798 13 = 7 ∧ acceleratedOrbit 13 2798 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2798 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2798) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2798.1, data_13_2798.2]

/-- Complete interval computation for depth 13, residue 2799. -/
theorem bounds_13_2799 : exactInterval 13 2799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2799 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2799) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2799 : oddCount 2799 13 = 9 ∧ acceleratedOrbit 13 2799 = 6728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2799 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2799) = 3 ^ 9 * m + 6728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2799.1, data_13_2799.2]

end Collatz.Research.StoppingAtlas.Batch0649
