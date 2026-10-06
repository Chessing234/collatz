import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0052

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 783. -/
theorem bounds_10_783 : exactInterval 10 783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_783 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 783) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_783 : oddCount 783 10 = 4 ∧ acceleratedOrbit 10 783 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_783 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 783) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_783.1, data_10_783.2]

/-- Complete interval computation for depth 10, residue 784. -/
theorem bounds_10_784 : exactInterval 10 784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_784 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 784) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_784 : oddCount 784 10 = 2 ∧ acceleratedOrbit 10 784 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_784 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 784) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_784.1, data_10_784.2]

/-- Complete interval computation for depth 10, residue 785. -/
theorem bounds_10_785 : exactInterval 10 785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_785 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 785) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_785 : oddCount 785 10 = 5 ∧ acceleratedOrbit 10 785 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_785 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 785) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_785.1, data_10_785.2]

/-- Complete interval computation for depth 10, residue 786. -/
theorem bounds_10_786 : exactInterval 10 786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_786 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 786) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_786 : oddCount 786 10 = 6 ∧ acceleratedOrbit 10 786 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_786 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 786) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_786.1, data_10_786.2]

/-- Complete interval computation for depth 10, residue 787. -/
theorem bounds_10_787 : exactInterval 10 787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_787 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 787) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_787 : oddCount 787 10 = 6 ∧ acceleratedOrbit 10 787 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_787 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 787) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_787.1, data_10_787.2]

/-- Complete interval computation for depth 10, residue 788. -/
theorem bounds_10_788 : exactInterval 10 788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_788 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 788) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_788 : oddCount 788 10 = 2 ∧ acceleratedOrbit 10 788 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_788 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 788) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_788.1, data_10_788.2]

/-- Complete interval computation for depth 10, residue 789. -/
theorem bounds_10_789 : exactInterval 10 789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_789 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 789) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_789 : oddCount 789 10 = 2 ∧ acceleratedOrbit 10 789 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_789 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 789) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_789.1, data_10_789.2]

/-- Complete interval computation for depth 10, residue 790. -/
theorem bounds_10_790 : exactInterval 10 790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_790 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 790) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_790 : oddCount 790 10 = 6 ∧ acceleratedOrbit 10 790 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_790 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 790) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_790.1, data_10_790.2]

/-- Complete interval computation for depth 10, residue 791. -/
theorem bounds_10_791 : exactInterval 10 791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_791 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 791) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_791 : oddCount 791 10 = 6 ∧ acceleratedOrbit 10 791 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_791 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 791) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_791.1, data_10_791.2]

/-- Complete interval computation for depth 10, residue 792. -/
theorem bounds_10_792 : exactInterval 10 792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_792 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 792) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_792 : oddCount 792 10 = 2 ∧ acceleratedOrbit 10 792 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_792 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 792) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_792.1, data_10_792.2]

/-- Complete interval computation for depth 10, residue 793. -/
theorem bounds_10_793 : exactInterval 10 793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_793 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 793) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_793 : oddCount 793 10 = 7 ∧ acceleratedOrbit 10 793 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_793 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 793) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_793.1, data_10_793.2]

/-- Complete interval computation for depth 10, residue 794. -/
theorem bounds_10_794 : exactInterval 10 794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_794 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 794) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_794 : oddCount 794 10 = 2 ∧ acceleratedOrbit 10 794 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_794 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 794) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_794.1, data_10_794.2]

/-- Complete interval computation for depth 10, residue 795. -/
theorem bounds_10_795 : exactInterval 10 795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_795 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 795) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_795 : oddCount 795 10 = 9 ∧ acceleratedOrbit 10 795 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_795 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 795) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_795.1, data_10_795.2]

/-- Complete interval computation for depth 10, residue 796. -/
theorem bounds_10_796 : exactInterval 10 796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_796 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 796) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_796 : oddCount 796 10 = 5 ∧ acceleratedOrbit 10 796 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_796 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 796) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_796.1, data_10_796.2]

/-- Complete interval computation for depth 10, residue 797. -/
theorem bounds_10_797 : exactInterval 10 797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_797 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 797) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_797 : oddCount 797 10 = 5 ∧ acceleratedOrbit 10 797 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_797 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 797) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_797.1, data_10_797.2]

end Collatz.Research.StoppingAtlas.Batch0052
