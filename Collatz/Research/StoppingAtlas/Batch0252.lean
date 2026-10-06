import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0252

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 783. -/
theorem bounds_12_783 : exactInterval 12 783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_783 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 783) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_783 : oddCount 783 12 = 5 ∧ acceleratedOrbit 12 783 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_783 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 783) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_783.1, data_12_783.2]

/-- Complete interval computation for depth 12, residue 784. -/
theorem bounds_12_784 : exactInterval 12 784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_784 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 784) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_784 : oddCount 784 12 = 4 ∧ acceleratedOrbit 12 784 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_784 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 784) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_784.1, data_12_784.2]

/-- Complete interval computation for depth 12, residue 785. -/
theorem bounds_12_785 : exactInterval 12 785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_785 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 785) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_785 : oddCount 785 12 = 5 ∧ acceleratedOrbit 12 785 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_785 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 785) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_785.1, data_12_785.2]

/-- Complete interval computation for depth 12, residue 786. -/
theorem bounds_12_786 : exactInterval 12 786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_786 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 786) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_786 : oddCount 786 12 = 7 ∧ acceleratedOrbit 12 786 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_786 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 786) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_786.1, data_12_786.2]

/-- Complete interval computation for depth 12, residue 787. -/
theorem bounds_12_787 : exactInterval 12 787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_787 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 787) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_787 : oddCount 787 12 = 7 ∧ acceleratedOrbit 12 787 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_787 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 787) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_787.1, data_12_787.2]

/-- Complete interval computation for depth 12, residue 788. -/
theorem bounds_12_788 : exactInterval 12 788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_788 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 788) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_788 : oddCount 788 12 = 4 ∧ acceleratedOrbit 12 788 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_788 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 788) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_788.1, data_12_788.2]

/-- Complete interval computation for depth 12, residue 789. -/
theorem bounds_12_789 : exactInterval 12 789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_789 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 789) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_789 : oddCount 789 12 = 4 ∧ acceleratedOrbit 12 789 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_789 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 789) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_789.1, data_12_789.2]

/-- Complete interval computation for depth 12, residue 790. -/
theorem bounds_12_790 : exactInterval 12 790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_790 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 790) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_790 : oddCount 790 12 = 7 ∧ acceleratedOrbit 12 790 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_790 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 790) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_790.1, data_12_790.2]

/-- Complete interval computation for depth 12, residue 791. -/
theorem bounds_12_791 : exactInterval 12 791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_791 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 791) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_791 : oddCount 791 12 = 7 ∧ acceleratedOrbit 12 791 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_791 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 791) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_791.1, data_12_791.2]

/-- Complete interval computation for depth 12, residue 792. -/
theorem bounds_12_792 : exactInterval 12 792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_792 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 792) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_792 : oddCount 792 12 = 4 ∧ acceleratedOrbit 12 792 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_792 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 792) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_792.1, data_12_792.2]

/-- Complete interval computation for depth 12, residue 793. -/
theorem bounds_12_793 : exactInterval 12 793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_793 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 793) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_793 : oddCount 793 12 = 7 ∧ acceleratedOrbit 12 793 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_793 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 793) = 3 ^ 7 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_793.1, data_12_793.2]

/-- Complete interval computation for depth 12, residue 794. -/
theorem bounds_12_794 : exactInterval 12 794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_794 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 794) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_794 : oddCount 794 12 = 4 ∧ acceleratedOrbit 12 794 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_794 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 794) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_794.1, data_12_794.2]

/-- Complete interval computation for depth 12, residue 795. -/
theorem bounds_12_795 : exactInterval 12 795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_795 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 795) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_795 : oddCount 795 12 = 9 ∧ acceleratedOrbit 12 795 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_795 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 795) = 3 ^ 9 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_795.1, data_12_795.2]

/-- Complete interval computation for depth 12, residue 796. -/
theorem bounds_12_796 : exactInterval 12 796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_796 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 796) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_796 : oddCount 796 12 = 6 ∧ acceleratedOrbit 12 796 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_796 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 796) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_796.1, data_12_796.2]

/-- Complete interval computation for depth 12, residue 797. -/
theorem bounds_12_797 : exactInterval 12 797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_797 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 797) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_797 : oddCount 797 12 = 6 ∧ acceleratedOrbit 12 797 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_797 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 797) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_797.1, data_12_797.2]

end Collatz.Research.StoppingAtlas.Batch0252
