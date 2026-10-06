import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0909

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6778. -/
theorem bounds_13_6778 : exactInterval 13 6778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6778 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6778) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6778 : oddCount 6778 13 = 6 ∧ acceleratedOrbit 13 6778 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6778 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6778) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6778.1, data_13_6778.2]

/-- Complete interval computation for depth 13, residue 6779. -/
theorem bounds_13_6779 : exactInterval 13 6779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6779 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6779) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6779 : oddCount 6779 13 = 7 ∧ acceleratedOrbit 13 6779 = 1811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6779 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6779) = 3 ^ 7 * m + 1811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6779.1, data_13_6779.2]

/-- Complete interval computation for depth 13, residue 6780. -/
theorem bounds_13_6780 : exactInterval 13 6780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6780 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6780) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6780 : oddCount 6780 13 = 9 ∧ acceleratedOrbit 13 6780 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6780 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6780) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6780.1, data_13_6780.2]

/-- Complete interval computation for depth 13, residue 6781. -/
theorem bounds_13_6781 : exactInterval 13 6781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6781 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6781) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6781 : oddCount 6781 13 = 9 ∧ acceleratedOrbit 13 6781 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6781 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6781) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6781.1, data_13_6781.2]

/-- Complete interval computation for depth 13, residue 6782. -/
theorem bounds_13_6782 : exactInterval 13 6782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6782 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6782) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6782 : oddCount 6782 13 = 9 ∧ acceleratedOrbit 13 6782 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6782 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6782) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6782.1, data_13_6782.2]

/-- Complete interval computation for depth 13, residue 6783. -/
theorem bounds_13_6783 : exactInterval 13 6783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6783 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6783) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6783 : oddCount 6783 13 = 9 ∧ acceleratedOrbit 13 6783 = 16300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6783 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6783) = 3 ^ 9 * m + 16300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6783.1, data_13_6783.2]

/-- Complete interval computation for depth 13, residue 6784. -/
theorem bounds_13_6784 : exactInterval 13 6784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6784 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6784) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6784 : oddCount 6784 13 = 2 ∧ acceleratedOrbit 13 6784 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6784 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6784) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6784.1, data_13_6784.2]

/-- Complete interval computation for depth 13, residue 6785. -/
theorem bounds_13_6785 : exactInterval 13 6785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6785 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6785) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6785 : oddCount 6785 13 = 8 ∧ acceleratedOrbit 13 6785 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6785 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6785) = 3 ^ 8 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6785.1, data_13_6785.2]

/-- Complete interval computation for depth 13, residue 6786. -/
theorem bounds_13_6786 : exactInterval 13 6786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6786 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6786) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6786 : oddCount 6786 13 = 5 ∧ acceleratedOrbit 13 6786 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6786 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6786) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6786.1, data_13_6786.2]

/-- Complete interval computation for depth 13, residue 6787. -/
theorem bounds_13_6787 : exactInterval 13 6787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6787 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6787) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6787 : oddCount 6787 13 = 5 ∧ acceleratedOrbit 13 6787 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6787 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6787) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6787.1, data_13_6787.2]

/-- Complete interval computation for depth 13, residue 6788. -/
theorem bounds_13_6788 : exactInterval 13 6788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6788 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6788) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6788 : oddCount 6788 13 = 6 ∧ acceleratedOrbit 13 6788 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6788 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6788) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6788.1, data_13_6788.2]

/-- Complete interval computation for depth 13, residue 6789. -/
theorem bounds_13_6789 : exactInterval 13 6789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6789 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6789) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6789 : oddCount 6789 13 = 6 ∧ acceleratedOrbit 13 6789 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6789 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6789) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6789.1, data_13_6789.2]

/-- Complete interval computation for depth 13, residue 6790. -/
theorem bounds_13_6790 : exactInterval 13 6790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6790 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6790) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6790 : oddCount 6790 13 = 6 ∧ acceleratedOrbit 13 6790 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6790 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6790) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6790.1, data_13_6790.2]

/-- Complete interval computation for depth 13, residue 6791. -/
theorem bounds_13_6791 : exactInterval 13 6791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6791 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6791) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6791 : oddCount 6791 13 = 6 ∧ acceleratedOrbit 13 6791 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6791 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6791) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6791.1, data_13_6791.2]

/-- Complete interval computation for depth 13, residue 6792. -/
theorem bounds_13_6792 : exactInterval 13 6792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6792 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6792) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6792 : oddCount 6792 13 = 6 ∧ acceleratedOrbit 13 6792 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6792 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6792) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6792.1, data_13_6792.2]

/-- Complete interval computation for depth 13, residue 6793. -/
theorem bounds_13_6793 : exactInterval 13 6793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6793 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6793) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6793 : oddCount 6793 13 = 7 ∧ acceleratedOrbit 13 6793 = 1814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6793 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6793) = 3 ^ 7 * m + 1814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6793.1, data_13_6793.2]

end Collatz.Research.StoppingAtlas.Batch0909
