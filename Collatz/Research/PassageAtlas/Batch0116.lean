import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0116

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3768. -/
theorem bounds_15_3768 : exactInterval 15 3768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3768 : oddCount 3768 15 = 7 ∧ acceleratedOrbit 15 3768 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3768) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3768.1, data_15_3768.2]

/-- Complete interval computation for depth 15, residue 3769. -/
theorem bounds_15_3769 : exactInterval 15 3769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3769 : oddCount 3769 15 = 10 ∧ acceleratedOrbit 15 3769 = 6803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3769) = 3 ^ 10 * m + 6803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3769.1, data_15_3769.2]

/-- Complete interval computation for depth 15, residue 3770. -/
theorem bounds_15_3770 : exactInterval 15 3770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3770 : oddCount 3770 15 = 7 ∧ acceleratedOrbit 15 3770 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3770) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3770.1, data_15_3770.2]

/-- Complete interval computation for depth 15, residue 3771. -/
theorem bounds_15_3771 : exactInterval 15 3771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3771 : oddCount 3771 15 = 10 ∧ acceleratedOrbit 15 3771 = 6803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3771) = 3 ^ 10 * m + 6803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3771.1, data_15_3771.2]

/-- Complete interval computation for depth 15, residue 3772. -/
theorem bounds_15_3772 : exactInterval 15 3772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3772 : oddCount 3772 15 = 5 ∧ acceleratedOrbit 15 3772 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3772) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3772.1, data_15_3772.2]

/-- Complete interval computation for depth 15, residue 3773. -/
theorem bounds_15_3773 : exactInterval 15 3773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3773 : oddCount 3773 15 = 5 ∧ acceleratedOrbit 15 3773 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3773) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3773.1, data_15_3773.2]

/-- Complete interval computation for depth 15, residue 3774. -/
theorem bounds_15_3774 : exactInterval 15 3774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3774 : oddCount 3774 15 = 5 ∧ acceleratedOrbit 15 3774 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3774) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3774.1, data_15_3774.2]

/-- Complete interval computation for depth 15, residue 3775. -/
theorem bounds_15_3775 : exactInterval 15 3775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3775 : oddCount 3775 15 = 10 ∧ acceleratedOrbit 15 3775 = 6805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3775) = 3 ^ 10 * m + 6805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3775.1, data_15_3775.2]

/-- Complete interval computation for depth 15, residue 3776. -/
theorem bounds_15_3776 : exactInterval 15 3776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3776 : oddCount 3776 15 = 5 ∧ acceleratedOrbit 15 3776 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3776) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3776.1, data_15_3776.2]

/-- Complete interval computation for depth 15, residue 3777. -/
theorem bounds_15_3777 : exactInterval 15 3777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3777 : oddCount 3777 15 = 7 ∧ acceleratedOrbit 15 3777 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3777) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3777.1, data_15_3777.2]

/-- Complete interval computation for depth 15, residue 3778. -/
theorem bounds_15_3778 : exactInterval 15 3778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3778 : oddCount 3778 15 = 8 ∧ acceleratedOrbit 15 3778 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3778) = 3 ^ 8 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3778.1, data_15_3778.2]

/-- Complete interval computation for depth 15, residue 3779. -/
theorem bounds_15_3779 : exactInterval 15 3779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3779 : oddCount 3779 15 = 8 ∧ acceleratedOrbit 15 3779 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3779) = 3 ^ 8 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3779.1, data_15_3779.2]

/-- Complete interval computation for depth 15, residue 3780. -/
theorem bounds_15_3780 : exactInterval 15 3780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3780 : oddCount 3780 15 = 5 ∧ acceleratedOrbit 15 3780 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3780) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3780.1, data_15_3780.2]

/-- Complete interval computation for depth 15, residue 3781. -/
theorem bounds_15_3781 : exactInterval 15 3781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3781 : oddCount 3781 15 = 5 ∧ acceleratedOrbit 15 3781 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3781) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3781.1, data_15_3781.2]

/-- Complete interval computation for depth 15, residue 3782. -/
theorem bounds_15_3782 : exactInterval 15 3782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3782 : oddCount 3782 15 = 5 ∧ acceleratedOrbit 15 3782 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3782) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3782.1, data_15_3782.2]

/-- Complete interval computation for depth 15, residue 3783. -/
theorem bounds_15_3783 : exactInterval 15 3783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3783 : oddCount 3783 15 = 7 ∧ acceleratedOrbit 15 3783 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3783) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3783.1, data_15_3783.2]

/-- Complete interval computation for depth 15, residue 3784. -/
theorem bounds_15_3784 : exactInterval 15 3784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3784 : oddCount 3784 15 = 5 ∧ acceleratedOrbit 15 3784 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3784) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3784.1, data_15_3784.2]

/-- Complete interval computation for depth 15, residue 3785. -/
theorem bounds_15_3785 : exactInterval 15 3785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3785 : oddCount 3785 15 = 7 ∧ acceleratedOrbit 15 3785 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3785) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3785.1, data_15_3785.2]

/-- Complete interval computation for depth 15, residue 3786. -/
theorem bounds_15_3786 : exactInterval 15 3786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3786 : oddCount 3786 15 = 5 ∧ acceleratedOrbit 15 3786 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3786) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3786.1, data_15_3786.2]

/-- Complete interval computation for depth 15, residue 3787. -/
theorem bounds_15_3787 : exactInterval 15 3787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3787 : oddCount 3787 15 = 9 ∧ acceleratedOrbit 15 3787 = 2278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3787) = 3 ^ 9 * m + 2278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3787.1, data_15_3787.2]

/-- Complete interval computation for depth 15, residue 3788. -/
theorem bounds_15_3788 : exactInterval 15 3788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3788 : oddCount 3788 15 = 5 ∧ acceleratedOrbit 15 3788 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3788) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3788.1, data_15_3788.2]

/-- Complete interval computation for depth 15, residue 3789. -/
theorem bounds_15_3789 : exactInterval 15 3789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3789 : oddCount 3789 15 = 5 ∧ acceleratedOrbit 15 3789 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3789) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3789.1, data_15_3789.2]

/-- Complete interval computation for depth 15, residue 3790. -/
theorem bounds_15_3790 : exactInterval 15 3790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3790 : oddCount 3790 15 = 11 ∧ acceleratedOrbit 15 3790 = 20503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3790) = 3 ^ 11 * m + 20503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3790.1, data_15_3790.2]

/-- Complete interval computation for depth 15, residue 3791. -/
theorem bounds_15_3791 : exactInterval 15 3791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3791 : oddCount 3791 15 = 11 ∧ acceleratedOrbit 15 3791 = 20503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3791) = 3 ^ 11 * m + 20503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3791.1, data_15_3791.2]

/-- Complete interval computation for depth 15, residue 3792. -/
theorem bounds_15_3792 : exactInterval 15 3792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3792 : oddCount 3792 15 = 5 ∧ acceleratedOrbit 15 3792 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3792) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3792.1, data_15_3792.2]

/-- Complete interval computation for depth 15, residue 3793. -/
theorem bounds_15_3793 : exactInterval 15 3793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3793 : oddCount 3793 15 = 7 ∧ acceleratedOrbit 15 3793 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3793) = 3 ^ 7 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3793.1, data_15_3793.2]

/-- Complete interval computation for depth 15, residue 3794. -/
theorem bounds_15_3794 : exactInterval 15 3794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3794 : oddCount 3794 15 = 7 ∧ acceleratedOrbit 15 3794 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3794) = 3 ^ 7 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3794.1, data_15_3794.2]

/-- Complete interval computation for depth 15, residue 3795. -/
theorem bounds_15_3795 : exactInterval 15 3795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3795 : oddCount 3795 15 = 7 ∧ acceleratedOrbit 15 3795 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3795) = 3 ^ 7 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3795.1, data_15_3795.2]

/-- Complete interval computation for depth 15, residue 3796. -/
theorem bounds_15_3796 : exactInterval 15 3796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3796 : oddCount 3796 15 = 5 ∧ acceleratedOrbit 15 3796 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3796) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3796.1, data_15_3796.2]

/-- Complete interval computation for depth 15, residue 3797. -/
theorem bounds_15_3797 : exactInterval 15 3797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3797 : oddCount 3797 15 = 5 ∧ acceleratedOrbit 15 3797 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3797) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3797.1, data_15_3797.2]

/-- Complete interval computation for depth 15, residue 3798. -/
theorem bounds_15_3798 : exactInterval 15 3798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3798 : oddCount 3798 15 = 7 ∧ acceleratedOrbit 15 3798 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3798) = 3 ^ 7 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3798.1, data_15_3798.2]

/-- Complete interval computation for depth 15, residue 3799. -/
theorem bounds_15_3799 : exactInterval 15 3799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3799 : oddCount 3799 15 = 7 ∧ acceleratedOrbit 15 3799 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3799) = 3 ^ 7 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3799.1, data_15_3799.2]

/-- Complete interval computation for depth 15, residue 3800. -/
theorem bounds_15_3800 : exactInterval 15 3800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3800 : oddCount 3800 15 = 6 ∧ acceleratedOrbit 15 3800 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3800) = 3 ^ 6 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3800.1, data_15_3800.2]

end Collatz.Research.PassageAtlas.Batch0116
