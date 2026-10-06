import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0452

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14778. -/
theorem bounds_15_14778 : exactInterval 15 14778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14778 : oddCount 14778 15 = 6 ∧ acceleratedOrbit 15 14778 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14778) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14778.1, data_15_14778.2]

/-- Complete interval computation for depth 15, residue 14779. -/
theorem bounds_15_14779 : exactInterval 15 14779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14779 : oddCount 14779 15 = 10 ∧ acceleratedOrbit 15 14779 = 26639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14779) = 3 ^ 10 * m + 26639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14779.1, data_15_14779.2]

/-- Complete interval computation for depth 15, residue 14780. -/
theorem bounds_15_14780 : exactInterval 15 14780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14780 : oddCount 14780 15 = 9 ∧ acceleratedOrbit 15 14780 = 8882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14780) = 3 ^ 9 * m + 8882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14780.1, data_15_14780.2]

/-- Complete interval computation for depth 15, residue 14781. -/
theorem bounds_15_14781 : exactInterval 15 14781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14781 : oddCount 14781 15 = 9 ∧ acceleratedOrbit 15 14781 = 8882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14781) = 3 ^ 9 * m + 8882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14781.1, data_15_14781.2]

/-- Complete interval computation for depth 15, residue 14782. -/
theorem bounds_15_14782 : exactInterval 15 14782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14782 : oddCount 14782 15 = 9 ∧ acceleratedOrbit 15 14782 = 8882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14782) = 3 ^ 9 * m + 8882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14782.1, data_15_14782.2]

/-- Complete interval computation for depth 15, residue 14783. -/
theorem bounds_15_14783 : exactInterval 15 14783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14783 : oddCount 14783 15 = 12 ∧ acceleratedOrbit 15 14783 = 239773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14783) = 3 ^ 12 * m + 239773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14783.1, data_15_14783.2]

/-- Complete interval computation for depth 15, residue 14784. -/
theorem bounds_15_14784 : exactInterval 15 14784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14784 : oddCount 14784 15 = 7 ∧ acceleratedOrbit 15 14784 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14784) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14784.1, data_15_14784.2]

/-- Complete interval computation for depth 15, residue 14785. -/
theorem bounds_15_14785 : exactInterval 15 14785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14785 : oddCount 14785 15 = 9 ∧ acceleratedOrbit 15 14785 = 8885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14785) = 3 ^ 9 * m + 8885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14785.1, data_15_14785.2]

/-- Complete interval computation for depth 15, residue 14786. -/
theorem bounds_15_14786 : exactInterval 15 14786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14786 : oddCount 14786 15 = 9 ∧ acceleratedOrbit 15 14786 = 8885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14786) = 3 ^ 9 * m + 8885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14786.1, data_15_14786.2]

/-- Complete interval computation for depth 15, residue 14787. -/
theorem bounds_15_14787 : exactInterval 15 14787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14787 : oddCount 14787 15 = 9 ∧ acceleratedOrbit 15 14787 = 8885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14787) = 3 ^ 9 * m + 8885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14787.1, data_15_14787.2]

/-- Complete interval computation for depth 15, residue 14788. -/
theorem bounds_15_14788 : exactInterval 15 14788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14788 : oddCount 14788 15 = 4 ∧ acceleratedOrbit 15 14788 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14788) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14788.1, data_15_14788.2]

/-- Complete interval computation for depth 15, residue 14789. -/
theorem bounds_15_14789 : exactInterval 15 14789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14789 : oddCount 14789 15 = 4 ∧ acceleratedOrbit 15 14789 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14789) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14789.1, data_15_14789.2]

/-- Complete interval computation for depth 15, residue 14790. -/
theorem bounds_15_14790 : exactInterval 15 14790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14790 : oddCount 14790 15 = 4 ∧ acceleratedOrbit 15 14790 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14790) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14790.1, data_15_14790.2]

/-- Complete interval computation for depth 15, residue 14791. -/
theorem bounds_15_14791 : exactInterval 15 14791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14791 : oddCount 14791 15 = 8 ∧ acceleratedOrbit 15 14791 = 2962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14791) = 3 ^ 8 * m + 2962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14791.1, data_15_14791.2]

/-- Complete interval computation for depth 15, residue 14792. -/
theorem bounds_15_14792 : exactInterval 15 14792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14792 : oddCount 14792 15 = 7 ∧ acceleratedOrbit 15 14792 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14792) = 3 ^ 7 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14792.1, data_15_14792.2]

/-- Complete interval computation for depth 15, residue 14793. -/
theorem bounds_15_14793 : exactInterval 15 14793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14793 : oddCount 14793 15 = 8 ∧ acceleratedOrbit 15 14793 = 2963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14793) = 3 ^ 8 * m + 2963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14793.1, data_15_14793.2]

/-- Complete interval computation for depth 15, residue 14794. -/
theorem bounds_15_14794 : exactInterval 15 14794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14794 : oddCount 14794 15 = 7 ∧ acceleratedOrbit 15 14794 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14794) = 3 ^ 7 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14794.1, data_15_14794.2]

/-- Complete interval computation for depth 15, residue 14795. -/
theorem bounds_15_14795 : exactInterval 15 14795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14795 : oddCount 14795 15 = 7 ∧ acceleratedOrbit 15 14795 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14795) = 3 ^ 7 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14795.1, data_15_14795.2]

/-- Complete interval computation for depth 15, residue 14796. -/
theorem bounds_15_14796 : exactInterval 15 14796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14796 : oddCount 14796 15 = 7 ∧ acceleratedOrbit 15 14796 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14796) = 3 ^ 7 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14796.1, data_15_14796.2]

/-- Complete interval computation for depth 15, residue 14797. -/
theorem bounds_15_14797 : exactInterval 15 14797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14797 : oddCount 14797 15 = 7 ∧ acceleratedOrbit 15 14797 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14797) = 3 ^ 7 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14797.1, data_15_14797.2]

/-- Complete interval computation for depth 15, residue 14798. -/
theorem bounds_15_14798 : exactInterval 15 14798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14798 : oddCount 14798 15 = 9 ∧ acceleratedOrbit 15 14798 = 8891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14798) = 3 ^ 9 * m + 8891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14798.1, data_15_14798.2]

/-- Complete interval computation for depth 15, residue 14799. -/
theorem bounds_15_14799 : exactInterval 15 14799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14799 : oddCount 14799 15 = 9 ∧ acceleratedOrbit 15 14799 = 8891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14799) = 3 ^ 9 * m + 8891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14799.1, data_15_14799.2]

/-- Complete interval computation for depth 15, residue 14800. -/
theorem bounds_15_14800 : exactInterval 15 14800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14800 : oddCount 14800 15 = 7 ∧ acceleratedOrbit 15 14800 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14800) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14800.1, data_15_14800.2]

/-- Complete interval computation for depth 15, residue 14801. -/
theorem bounds_15_14801 : exactInterval 15 14801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14801 : oddCount 14801 15 = 7 ∧ acceleratedOrbit 15 14801 = 989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14801) = 3 ^ 7 * m + 989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14801.1, data_15_14801.2]

/-- Complete interval computation for depth 15, residue 14802. -/
theorem bounds_15_14802 : exactInterval 15 14802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14802 : oddCount 14802 15 = 8 ∧ acceleratedOrbit 15 14802 = 2965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14802) = 3 ^ 8 * m + 2965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14802.1, data_15_14802.2]

/-- Complete interval computation for depth 15, residue 14803. -/
theorem bounds_15_14803 : exactInterval 15 14803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14803 : oddCount 14803 15 = 8 ∧ acceleratedOrbit 15 14803 = 2965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14803) = 3 ^ 8 * m + 2965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14803.1, data_15_14803.2]

/-- Complete interval computation for depth 15, residue 14804. -/
theorem bounds_15_14804 : exactInterval 15 14804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14804 : oddCount 14804 15 = 7 ∧ acceleratedOrbit 15 14804 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14804) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14804.1, data_15_14804.2]

/-- Complete interval computation for depth 15, residue 14805. -/
theorem bounds_15_14805 : exactInterval 15 14805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14805 : oddCount 14805 15 = 7 ∧ acceleratedOrbit 15 14805 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14805) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14805.1, data_15_14805.2]

/-- Complete interval computation for depth 15, residue 14806. -/
theorem bounds_15_14806 : exactInterval 15 14806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14806 : oddCount 14806 15 = 10 ∧ acceleratedOrbit 15 14806 = 26689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14806) = 3 ^ 10 * m + 26689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14806.1, data_15_14806.2]

/-- Complete interval computation for depth 15, residue 14807. -/
theorem bounds_15_14807 : exactInterval 15 14807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14807 : oddCount 14807 15 = 10 ∧ acceleratedOrbit 15 14807 = 26689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14807) = 3 ^ 10 * m + 26689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14807.1, data_15_14807.2]

/-- Complete interval computation for depth 15, residue 14808. -/
theorem bounds_15_14808 : exactInterval 15 14808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14808 : oddCount 14808 15 = 5 ∧ acceleratedOrbit 15 14808 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14808) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14808.1, data_15_14808.2]

/-- Complete interval computation for depth 15, residue 14809. -/
theorem bounds_15_14809 : exactInterval 15 14809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14809 : oddCount 14809 15 = 5 ∧ acceleratedOrbit 15 14809 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14809) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14809.1, data_15_14809.2]

/-- Complete interval computation for depth 15, residue 14810. -/
theorem bounds_15_14810 : exactInterval 15 14810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14810 : oddCount 14810 15 = 5 ∧ acceleratedOrbit 15 14810 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14810) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14810.1, data_15_14810.2]

end Collatz.Research.PassageAtlas.Batch0452
