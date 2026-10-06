import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0447

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3778. -/
theorem bounds_12_3778 : exactInterval 12 3778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3778 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3778) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3778 : oddCount 3778 12 = 7 ∧ acceleratedOrbit 12 3778 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3778 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3778) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3778.1, data_12_3778.2]

/-- Complete interval computation for depth 12, residue 3779. -/
theorem bounds_12_3779 : exactInterval 12 3779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3779 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3779) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3779 : oddCount 3779 12 = 7 ∧ acceleratedOrbit 12 3779 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3779 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3779) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3779.1, data_12_3779.2]

/-- Complete interval computation for depth 12, residue 3780. -/
theorem bounds_12_3780 : exactInterval 12 3780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3780 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3780) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3780 : oddCount 3780 12 = 3 ∧ acceleratedOrbit 12 3780 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3780 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3780) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3780.1, data_12_3780.2]

/-- Complete interval computation for depth 12, residue 3781. -/
theorem bounds_12_3781 : exactInterval 12 3781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3781 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3781) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3781 : oddCount 3781 12 = 3 ∧ acceleratedOrbit 12 3781 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3781 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3781) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3781.1, data_12_3781.2]

/-- Complete interval computation for depth 12, residue 3782. -/
theorem bounds_12_3782 : exactInterval 12 3782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3782 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3782) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3782 : oddCount 3782 12 = 3 ∧ acceleratedOrbit 12 3782 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3782 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3782) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3782.1, data_12_3782.2]

/-- Complete interval computation for depth 12, residue 3783. -/
theorem bounds_12_3783 : exactInterval 12 3783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3783 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3783) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3783 : oddCount 3783 12 = 6 ∧ acceleratedOrbit 12 3783 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3783 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3783) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3783.1, data_12_3783.2]

/-- Complete interval computation for depth 12, residue 3784. -/
theorem bounds_12_3784 : exactInterval 12 3784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3784 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3784) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3784 : oddCount 3784 12 = 3 ∧ acceleratedOrbit 12 3784 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3784 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3784) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3784.1, data_12_3784.2]

/-- Complete interval computation for depth 12, residue 3785. -/
theorem bounds_12_3785 : exactInterval 12 3785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3785 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3785) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3785 : oddCount 3785 12 = 7 ∧ acceleratedOrbit 12 3785 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3785 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3785) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3785.1, data_12_3785.2]

/-- Complete interval computation for depth 12, residue 3786. -/
theorem bounds_12_3786 : exactInterval 12 3786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3786 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3786) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3786 : oddCount 3786 12 = 3 ∧ acceleratedOrbit 12 3786 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3786 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3786) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3786.1, data_12_3786.2]

/-- Complete interval computation for depth 12, residue 3787. -/
theorem bounds_12_3787 : exactInterval 12 3787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3787 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3787) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3787 : oddCount 3787 12 = 8 ∧ acceleratedOrbit 12 3787 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3787 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3787) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3787.1, data_12_3787.2]

/-- Complete interval computation for depth 12, residue 3788. -/
theorem bounds_12_3788 : exactInterval 12 3788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3788 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3788) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3788 : oddCount 3788 12 = 3 ∧ acceleratedOrbit 12 3788 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3788 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3788) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3788.1, data_12_3788.2]

/-- Complete interval computation for depth 12, residue 3789. -/
theorem bounds_12_3789 : exactInterval 12 3789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3789 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3789) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3789 : oddCount 3789 12 = 3 ∧ acceleratedOrbit 12 3789 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3789 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3789) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3789.1, data_12_3789.2]

/-- Complete interval computation for depth 12, residue 3790. -/
theorem bounds_12_3790 : exactInterval 12 3790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3790 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3790) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3790 : oddCount 3790 12 = 10 ∧ acceleratedOrbit 12 3790 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3790 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3790) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3790.1, data_12_3790.2]

/-- Complete interval computation for depth 12, residue 3791. -/
theorem bounds_12_3791 : exactInterval 12 3791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3791 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3791) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3791 : oddCount 3791 12 = 10 ∧ acceleratedOrbit 12 3791 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3791 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3791) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3791.1, data_12_3791.2]

/-- Complete interval computation for depth 12, residue 3792. -/
theorem bounds_12_3792 : exactInterval 12 3792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3792 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3792) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3792 : oddCount 3792 12 = 4 ∧ acceleratedOrbit 12 3792 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3792 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3792) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3792.1, data_12_3792.2]

end Collatz.Research.StoppingAtlas.Batch0447
