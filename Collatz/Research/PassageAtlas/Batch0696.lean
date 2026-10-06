import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0696

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22773. -/
theorem bounds_15_22773 : exactInterval 15 22773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22773 : oddCount 22773 15 = 5 ∧ acceleratedOrbit 15 22773 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22773) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22773.1, data_15_22773.2]

/-- Complete interval computation for depth 15, residue 22774. -/
theorem bounds_15_22774 : exactInterval 15 22774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22774 : oddCount 22774 15 = 8 ∧ acceleratedOrbit 15 22774 = 4562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22774) = 3 ^ 8 * m + 4562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22774.1, data_15_22774.2]

/-- Complete interval computation for depth 15, residue 22775. -/
theorem bounds_15_22775 : exactInterval 15 22775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22775 : oddCount 22775 15 = 8 ∧ acceleratedOrbit 15 22775 = 4562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22775) = 3 ^ 8 * m + 4562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22775.1, data_15_22775.2]

/-- Complete interval computation for depth 15, residue 22776. -/
theorem bounds_15_22776 : exactInterval 15 22776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22776 : oddCount 22776 15 = 9 ∧ acceleratedOrbit 15 22776 = 13688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22776) = 3 ^ 9 * m + 13688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22776.1, data_15_22776.2]

/-- Complete interval computation for depth 15, residue 22777. -/
theorem bounds_15_22777 : exactInterval 15 22777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22777 : oddCount 22777 15 = 9 ∧ acceleratedOrbit 15 22777 = 13684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22777) = 3 ^ 9 * m + 13684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22777.1, data_15_22777.2]

/-- Complete interval computation for depth 15, residue 22778. -/
theorem bounds_15_22778 : exactInterval 15 22778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22778 : oddCount 22778 15 = 9 ∧ acceleratedOrbit 15 22778 = 13688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22778) = 3 ^ 9 * m + 13688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22778.1, data_15_22778.2]

/-- Complete interval computation for depth 15, residue 22779. -/
theorem bounds_15_22779 : exactInterval 15 22779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22779 : oddCount 22779 15 = 12 ∧ acceleratedOrbit 15 22779 = 369467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22779) = 3 ^ 12 * m + 369467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22779.1, data_15_22779.2]

/-- Complete interval computation for depth 15, residue 22780. -/
theorem bounds_15_22780 : exactInterval 15 22780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22780 : oddCount 22780 15 = 9 ∧ acceleratedOrbit 15 22780 = 13688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22780) = 3 ^ 9 * m + 13688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22780.1, data_15_22780.2]

/-- Complete interval computation for depth 15, residue 22781. -/
theorem bounds_15_22781 : exactInterval 15 22781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22781 : oddCount 22781 15 = 9 ∧ acceleratedOrbit 15 22781 = 13688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22781) = 3 ^ 9 * m + 13688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22781.1, data_15_22781.2]

/-- Complete interval computation for depth 15, residue 22782. -/
theorem bounds_15_22782 : exactInterval 15 22782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22782 : oddCount 22782 15 = 12 ∧ acceleratedOrbit 15 22782 = 369521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22782) = 3 ^ 12 * m + 369521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22782.1, data_15_22782.2]

/-- Complete interval computation for depth 15, residue 22783. -/
theorem bounds_15_22783 : exactInterval 15 22783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22783 : oddCount 22783 15 = 12 ∧ acceleratedOrbit 15 22783 = 369521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22783) = 3 ^ 12 * m + 369521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22783.1, data_15_22783.2]

/-- Complete interval computation for depth 15, residue 22784. -/
theorem bounds_15_22784 : exactInterval 15 22784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22784 : oddCount 22784 15 = 3 ∧ acceleratedOrbit 15 22784 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22784) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22784.1, data_15_22784.2]

/-- Complete interval computation for depth 15, residue 22785. -/
theorem bounds_15_22785 : exactInterval 15 22785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22785 : oddCount 22785 15 = 5 ∧ acceleratedOrbit 15 22785 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22785) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22785.1, data_15_22785.2]

/-- Complete interval computation for depth 15, residue 22786. -/
theorem bounds_15_22786 : exactInterval 15 22786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22786 : oddCount 22786 15 = 8 ∧ acceleratedOrbit 15 22786 = 4564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22786) = 3 ^ 8 * m + 4564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22786.1, data_15_22786.2]

/-- Complete interval computation for depth 15, residue 22787. -/
theorem bounds_15_22787 : exactInterval 15 22787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22787 : oddCount 22787 15 = 8 ∧ acceleratedOrbit 15 22787 = 4564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22787) = 3 ^ 8 * m + 4564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22787.1, data_15_22787.2]

/-- Complete interval computation for depth 15, residue 22788. -/
theorem bounds_15_22788 : exactInterval 15 22788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22788 : oddCount 22788 15 = 6 ∧ acceleratedOrbit 15 22788 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22788) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22788.1, data_15_22788.2]

/-- Complete interval computation for depth 15, residue 22789. -/
theorem bounds_15_22789 : exactInterval 15 22789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22789 : oddCount 22789 15 = 6 ∧ acceleratedOrbit 15 22789 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22789) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22789.1, data_15_22789.2]

/-- Complete interval computation for depth 15, residue 22790. -/
theorem bounds_15_22790 : exactInterval 15 22790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22790 : oddCount 22790 15 = 6 ∧ acceleratedOrbit 15 22790 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22790) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22790.1, data_15_22790.2]

/-- Complete interval computation for depth 15, residue 22791. -/
theorem bounds_15_22791 : exactInterval 15 22791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22791 : oddCount 22791 15 = 8 ∧ acceleratedOrbit 15 22791 = 4564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22791) = 3 ^ 8 * m + 4564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22791.1, data_15_22791.2]

/-- Complete interval computation for depth 15, residue 22792. -/
theorem bounds_15_22792 : exactInterval 15 22792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22792 : oddCount 22792 15 = 6 ∧ acceleratedOrbit 15 22792 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22792) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22792.1, data_15_22792.2]

/-- Complete interval computation for depth 15, residue 22793. -/
theorem bounds_15_22793 : exactInterval 15 22793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22793 : oddCount 22793 15 = 8 ∧ acceleratedOrbit 15 22793 = 4565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22793) = 3 ^ 8 * m + 4565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22793.1, data_15_22793.2]

/-- Complete interval computation for depth 15, residue 22794. -/
theorem bounds_15_22794 : exactInterval 15 22794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22794 : oddCount 22794 15 = 6 ∧ acceleratedOrbit 15 22794 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22794) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22794.1, data_15_22794.2]

/-- Complete interval computation for depth 15, residue 22795. -/
theorem bounds_15_22795 : exactInterval 15 22795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22795 : oddCount 22795 15 = 7 ∧ acceleratedOrbit 15 22795 = 1522 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22795) = 3 ^ 7 * m + 1522 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22795.1, data_15_22795.2]

/-- Complete interval computation for depth 15, residue 22796. -/
theorem bounds_15_22796 : exactInterval 15 22796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22796 : oddCount 22796 15 = 6 ∧ acceleratedOrbit 15 22796 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22796) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22796.1, data_15_22796.2]

/-- Complete interval computation for depth 15, residue 22797. -/
theorem bounds_15_22797 : exactInterval 15 22797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22797 : oddCount 22797 15 = 6 ∧ acceleratedOrbit 15 22797 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22797) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22797.1, data_15_22797.2]

/-- Complete interval computation for depth 15, residue 22798. -/
theorem bounds_15_22798 : exactInterval 15 22798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22798 : oddCount 22798 15 = 7 ∧ acceleratedOrbit 15 22798 = 1522 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22798) = 3 ^ 7 * m + 1522 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22798.1, data_15_22798.2]

/-- Complete interval computation for depth 15, residue 22799. -/
theorem bounds_15_22799 : exactInterval 15 22799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22799 : oddCount 22799 15 = 7 ∧ acceleratedOrbit 15 22799 = 1522 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22799) = 3 ^ 7 * m + 1522 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22799.1, data_15_22799.2]

/-- Complete interval computation for depth 15, residue 22800. -/
theorem bounds_15_22800 : exactInterval 15 22800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22800 : oddCount 22800 15 = 5 ∧ acceleratedOrbit 15 22800 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22800) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22800.1, data_15_22800.2]

/-- Complete interval computation for depth 15, residue 22801. -/
theorem bounds_15_22801 : exactInterval 15 22801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22801 : oddCount 22801 15 = 6 ∧ acceleratedOrbit 15 22801 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22801) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22801.1, data_15_22801.2]

/-- Complete interval computation for depth 15, residue 22802. -/
theorem bounds_15_22802 : exactInterval 15 22802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22802 : oddCount 22802 15 = 9 ∧ acceleratedOrbit 15 22802 = 13699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22802) = 3 ^ 9 * m + 13699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22802.1, data_15_22802.2]

/-- Complete interval computation for depth 15, residue 22803. -/
theorem bounds_15_22803 : exactInterval 15 22803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22803 : oddCount 22803 15 = 9 ∧ acceleratedOrbit 15 22803 = 13699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22803) = 3 ^ 9 * m + 13699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22803.1, data_15_22803.2]

/-- Complete interval computation for depth 15, residue 22804. -/
theorem bounds_15_22804 : exactInterval 15 22804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22804 : oddCount 22804 15 = 5 ∧ acceleratedOrbit 15 22804 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22804) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22804.1, data_15_22804.2]

/-- Complete interval computation for depth 15, residue 22805. -/
theorem bounds_15_22805 : exactInterval 15 22805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22805 : oddCount 22805 15 = 5 ∧ acceleratedOrbit 15 22805 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22805) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22805.1, data_15_22805.2]

end Collatz.Research.PassageAtlas.Batch0696
