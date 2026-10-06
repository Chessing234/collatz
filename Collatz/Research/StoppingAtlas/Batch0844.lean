import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0844

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5780. -/
theorem bounds_13_5780 : exactInterval 13 5780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5780 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5780) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5780 : oddCount 5780 13 = 5 ∧ acceleratedOrbit 13 5780 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5780 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5780) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5780.1, data_13_5780.2]

/-- Complete interval computation for depth 13, residue 5781. -/
theorem bounds_13_5781 : exactInterval 13 5781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5781 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5781) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5781 : oddCount 5781 13 = 5 ∧ acceleratedOrbit 13 5781 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5781 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5781) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5781.1, data_13_5781.2]

/-- Complete interval computation for depth 13, residue 5782. -/
theorem bounds_13_5782 : exactInterval 13 5782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5782 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5782) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5782 : oddCount 5782 13 = 5 ∧ acceleratedOrbit 13 5782 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5782 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5782) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5782.1, data_13_5782.2]

/-- Complete interval computation for depth 13, residue 5783. -/
theorem bounds_13_5783 : exactInterval 13 5783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5783 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5783) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5783 : oddCount 5783 13 = 5 ∧ acceleratedOrbit 13 5783 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5783 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5783) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5783.1, data_13_5783.2]

/-- Complete interval computation for depth 13, residue 5784. -/
theorem bounds_13_5784 : exactInterval 13 5784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5784 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5784) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5784 : oddCount 5784 13 = 5 ∧ acceleratedOrbit 13 5784 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5784 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5784) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5784.1, data_13_5784.2]

/-- Complete interval computation for depth 13, residue 5785. -/
theorem bounds_13_5785 : exactInterval 13 5785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5785 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5785) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5785 : oddCount 5785 13 = 8 ∧ acceleratedOrbit 13 5785 = 4637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5785 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5785) = 3 ^ 8 * m + 4637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5785.1, data_13_5785.2]

/-- Complete interval computation for depth 13, residue 5786. -/
theorem bounds_13_5786 : exactInterval 13 5786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5786 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5786) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5786 : oddCount 5786 13 = 5 ∧ acceleratedOrbit 13 5786 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5786 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5786) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5786.1, data_13_5786.2]

/-- Complete interval computation for depth 13, residue 5787. -/
theorem bounds_13_5787 : exactInterval 13 5787 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5787 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5787) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5787 : oddCount 5787 13 = 8 ∧ acceleratedOrbit 13 5787 = 4636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5787 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5787) = 3 ^ 8 * m + 4636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5787.1, data_13_5787.2]

/-- Complete interval computation for depth 13, residue 5788. -/
theorem bounds_13_5788 : exactInterval 13 5788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5788 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5788) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5788 : oddCount 5788 13 = 7 ∧ acceleratedOrbit 13 5788 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5788 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5788) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5788.1, data_13_5788.2]

/-- Complete interval computation for depth 13, residue 5789. -/
theorem bounds_13_5789 : exactInterval 13 5789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5789 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5789) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5789 : oddCount 5789 13 = 7 ∧ acceleratedOrbit 13 5789 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5789 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5789) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5789.1, data_13_5789.2]

/-- Complete interval computation for depth 13, residue 5790. -/
theorem bounds_13_5790 : exactInterval 13 5790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5790 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5790) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5790 : oddCount 5790 13 = 7 ∧ acceleratedOrbit 13 5790 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5790 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5790) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5790.1, data_13_5790.2]

/-- Complete interval computation for depth 13, residue 5791. -/
theorem bounds_13_5791 : exactInterval 13 5791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5791 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5791) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5791 : oddCount 5791 13 = 11 ∧ acceleratedOrbit 13 5791 = 125252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5791 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5791) = 3 ^ 11 * m + 125252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5791.1, data_13_5791.2]

/-- Complete interval computation for depth 13, residue 5792. -/
theorem bounds_13_5792 : exactInterval 13 5792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5792 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5792) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5792 : oddCount 5792 13 = 3 ∧ acceleratedOrbit 13 5792 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5792 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5792) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5792.1, data_13_5792.2]

/-- Complete interval computation for depth 13, residue 5793. -/
theorem bounds_13_5793 : exactInterval 13 5793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5793 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5793) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5793 : oddCount 5793 13 = 8 ∧ acceleratedOrbit 13 5793 = 4643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5793 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5793) = 3 ^ 8 * m + 4643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5793.1, data_13_5793.2]

/-- Complete interval computation for depth 13, residue 5794. -/
theorem bounds_13_5794 : exactInterval 13 5794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5794 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5794) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5794 : oddCount 5794 13 = 7 ∧ acceleratedOrbit 13 5794 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5794 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5794) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5794.1, data_13_5794.2]

end Collatz.Research.StoppingAtlas.Batch0844
