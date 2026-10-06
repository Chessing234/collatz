import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0714

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3783. -/
theorem bounds_13_3783 : exactInterval 13 3783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3783 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3783) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3783 : oddCount 3783 13 = 6 ∧ acceleratedOrbit 13 3783 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3783 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3783) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3783.1, data_13_3783.2]

/-- Complete interval computation for depth 13, residue 3784. -/
theorem bounds_13_3784 : exactInterval 13 3784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3784 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3784) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3784 : oddCount 3784 13 = 4 ∧ acceleratedOrbit 13 3784 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3784 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3784) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3784.1, data_13_3784.2]

/-- Complete interval computation for depth 13, residue 3785. -/
theorem bounds_13_3785 : exactInterval 13 3785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3785 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3785) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3785 : oddCount 3785 13 = 7 ∧ acceleratedOrbit 13 3785 = 1012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3785 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3785) = 3 ^ 7 * m + 1012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3785.1, data_13_3785.2]

/-- Complete interval computation for depth 13, residue 3786. -/
theorem bounds_13_3786 : exactInterval 13 3786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3786 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3786) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3786 : oddCount 3786 13 = 4 ∧ acceleratedOrbit 13 3786 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3786 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3786) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3786.1, data_13_3786.2]

/-- Complete interval computation for depth 13, residue 3787. -/
theorem bounds_13_3787 : exactInterval 13 3787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3787 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3787) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3787 : oddCount 3787 13 = 8 ∧ acceleratedOrbit 13 3787 = 3037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3787 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3787) = 3 ^ 8 * m + 3037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3787.1, data_13_3787.2]

/-- Complete interval computation for depth 13, residue 3788. -/
theorem bounds_13_3788 : exactInterval 13 3788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3788 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3788) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3788 : oddCount 3788 13 = 4 ∧ acceleratedOrbit 13 3788 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3788 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3788) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3788.1, data_13_3788.2]

/-- Complete interval computation for depth 13, residue 3789. -/
theorem bounds_13_3789 : exactInterval 13 3789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3789 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3789) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3789 : oddCount 3789 13 = 4 ∧ acceleratedOrbit 13 3789 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3789 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3789) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3789.1, data_13_3789.2]

/-- Complete interval computation for depth 13, residue 3790. -/
theorem bounds_13_3790 : exactInterval 13 3790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3790 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3790) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3790 : oddCount 3790 13 = 10 ∧ acceleratedOrbit 13 3790 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3790 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3790) = 3 ^ 10 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3790.1, data_13_3790.2]

/-- Complete interval computation for depth 13, residue 3791. -/
theorem bounds_13_3791 : exactInterval 13 3791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3791 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3791) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3791 : oddCount 3791 13 = 10 ∧ acceleratedOrbit 13 3791 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3791 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3791) = 3 ^ 10 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3791.1, data_13_3791.2]

/-- Complete interval computation for depth 13, residue 3792. -/
theorem bounds_13_3792 : exactInterval 13 3792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3792 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3792) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3792 : oddCount 3792 13 = 4 ∧ acceleratedOrbit 13 3792 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3792 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3792) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3792.1, data_13_3792.2]

/-- Complete interval computation for depth 13, residue 3793. -/
theorem bounds_13_3793 : exactInterval 13 3793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3793 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3793) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3793 : oddCount 3793 13 = 6 ∧ acceleratedOrbit 13 3793 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3793 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3793) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3793.1, data_13_3793.2]

/-- Complete interval computation for depth 13, residue 3794. -/
theorem bounds_13_3794 : exactInterval 13 3794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3794 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3794) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3794 : oddCount 3794 13 = 6 ∧ acceleratedOrbit 13 3794 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3794 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3794) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3794.1, data_13_3794.2]

/-- Complete interval computation for depth 13, residue 3795. -/
theorem bounds_13_3795 : exactInterval 13 3795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3795 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3795) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3795 : oddCount 3795 13 = 6 ∧ acceleratedOrbit 13 3795 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3795 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3795) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3795.1, data_13_3795.2]

/-- Complete interval computation for depth 13, residue 3796. -/
theorem bounds_13_3796 : exactInterval 13 3796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3796 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3796) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3796 : oddCount 3796 13 = 4 ∧ acceleratedOrbit 13 3796 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3796 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3796) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3796.1, data_13_3796.2]

/-- Complete interval computation for depth 13, residue 3797. -/
theorem bounds_13_3797 : exactInterval 13 3797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3797 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3797) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3797 : oddCount 3797 13 = 4 ∧ acceleratedOrbit 13 3797 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3797 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3797) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3797.1, data_13_3797.2]

/-- Complete interval computation for depth 13, residue 3798. -/
theorem bounds_13_3798 : exactInterval 13 3798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3798 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3798) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3798 : oddCount 3798 13 = 7 ∧ acceleratedOrbit 13 3798 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3798 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3798) = 3 ^ 7 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3798.1, data_13_3798.2]

end Collatz.Research.StoppingAtlas.Batch0714
