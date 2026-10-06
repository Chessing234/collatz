import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0779

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4782. -/
theorem bounds_13_4782 : exactInterval 13 4782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4782 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4782) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4782 : oddCount 4782 13 = 5 ∧ acceleratedOrbit 13 4782 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4782 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4782) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4782.1, data_13_4782.2]

/-- Complete interval computation for depth 13, residue 4783. -/
theorem bounds_13_4783 : exactInterval 13 4783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4783 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4783) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4783 : oddCount 4783 13 = 8 ∧ acceleratedOrbit 13 4783 = 3833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4783 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4783) = 3 ^ 8 * m + 3833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4783.1, data_13_4783.2]

/-- Complete interval computation for depth 13, residue 4784. -/
theorem bounds_13_4784 : exactInterval 13 4784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4784 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4784) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4784 : oddCount 4784 13 = 5 ∧ acceleratedOrbit 13 4784 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4784 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4784) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4784.1, data_13_4784.2]

/-- Complete interval computation for depth 13, residue 4785. -/
theorem bounds_13_4785 : exactInterval 13 4785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4785 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4785) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4785 : oddCount 4785 13 = 6 ∧ acceleratedOrbit 13 4785 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4785 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4785) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4785.1, data_13_4785.2]

/-- Complete interval computation for depth 13, residue 4786. -/
theorem bounds_13_4786 : exactInterval 13 4786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4786 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4786) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4786 : oddCount 4786 13 = 6 ∧ acceleratedOrbit 13 4786 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4786 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4786) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4786.1, data_13_4786.2]

/-- Complete interval computation for depth 13, residue 4787. -/
theorem bounds_13_4787 : exactInterval 13 4787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4787 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4787) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4787 : oddCount 4787 13 = 6 ∧ acceleratedOrbit 13 4787 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4787 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4787) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4787.1, data_13_4787.2]

/-- Complete interval computation for depth 13, residue 4788. -/
theorem bounds_13_4788 : exactInterval 13 4788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4788 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4788) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4788 : oddCount 4788 13 = 5 ∧ acceleratedOrbit 13 4788 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4788 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4788) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4788.1, data_13_4788.2]

/-- Complete interval computation for depth 13, residue 4789. -/
theorem bounds_13_4789 : exactInterval 13 4789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4789 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4789) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4789 : oddCount 4789 13 = 5 ∧ acceleratedOrbit 13 4789 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4789 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4789) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4789.1, data_13_4789.2]

/-- Complete interval computation for depth 13, residue 4790. -/
theorem bounds_13_4790 : exactInterval 13 4790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4790 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4790) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4790 : oddCount 4790 13 = 7 ∧ acceleratedOrbit 13 4790 = 1280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4790 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4790) = 3 ^ 7 * m + 1280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4790.1, data_13_4790.2]

/-- Complete interval computation for depth 13, residue 4791. -/
theorem bounds_13_4791 : exactInterval 13 4791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4791 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4791) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4791 : oddCount 4791 13 = 7 ∧ acceleratedOrbit 13 4791 = 1280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4791 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4791) = 3 ^ 7 * m + 1280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4791.1, data_13_4791.2]

/-- Complete interval computation for depth 13, residue 4792. -/
theorem bounds_13_4792 : exactInterval 13 4792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4792 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4792) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4792 : oddCount 4792 13 = 5 ∧ acceleratedOrbit 13 4792 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4792 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4792) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4792.1, data_13_4792.2]

/-- Complete interval computation for depth 13, residue 4793. -/
theorem bounds_13_4793 : exactInterval 13 4793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4793 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4793) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4793 : oddCount 4793 13 = 6 ∧ acceleratedOrbit 13 4793 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4793 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4793) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4793.1, data_13_4793.2]

/-- Complete interval computation for depth 13, residue 4794. -/
theorem bounds_13_4794 : exactInterval 13 4794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4794 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4794) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4794 : oddCount 4794 13 = 5 ∧ acceleratedOrbit 13 4794 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4794 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4794) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4794.1, data_13_4794.2]

/-- Complete interval computation for depth 13, residue 4795. -/
theorem bounds_13_4795 : exactInterval 13 4795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4795 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4795) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4795 : oddCount 4795 13 = 9 ∧ acceleratedOrbit 13 4795 = 11528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4795 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4795) = 3 ^ 9 * m + 11528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4795.1, data_13_4795.2]

/-- Complete interval computation for depth 13, residue 4796. -/
theorem bounds_13_4796 : exactInterval 13 4796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4796 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4796) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4796 : oddCount 4796 13 = 7 ∧ acceleratedOrbit 13 4796 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4796 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4796) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4796.1, data_13_4796.2]

end Collatz.Research.StoppingAtlas.Batch0779
