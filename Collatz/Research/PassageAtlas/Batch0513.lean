import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0513

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16777. -/
theorem bounds_15_16777 : exactInterval 15 16777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16777 : oddCount 16777 15 = 10 ∧ acceleratedOrbit 15 16777 = 30239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16777) = 3 ^ 10 * m + 30239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16777.1, data_15_16777.2]

/-- Complete interval computation for depth 15, residue 16778. -/
theorem bounds_15_16778 : exactInterval 15 16778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16778 : oddCount 16778 15 = 7 ∧ acceleratedOrbit 15 16778 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16778) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16778.1, data_15_16778.2]

/-- Complete interval computation for depth 15, residue 16779. -/
theorem bounds_15_16779 : exactInterval 15 16779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16779 : oddCount 16779 15 = 9 ∧ acceleratedOrbit 15 16779 = 10081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16779) = 3 ^ 9 * m + 10081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16779.1, data_15_16779.2]

/-- Complete interval computation for depth 15, residue 16780. -/
theorem bounds_15_16780 : exactInterval 15 16780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16780 : oddCount 16780 15 = 7 ∧ acceleratedOrbit 15 16780 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16780) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16780.1, data_15_16780.2]

/-- Complete interval computation for depth 15, residue 16781. -/
theorem bounds_15_16781 : exactInterval 15 16781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16781 : oddCount 16781 15 = 7 ∧ acceleratedOrbit 15 16781 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16781) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16781.1, data_15_16781.2]

/-- Complete interval computation for depth 15, residue 16782. -/
theorem bounds_15_16782 : exactInterval 15 16782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16782 : oddCount 16782 15 = 9 ∧ acceleratedOrbit 15 16782 = 10084 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16782) = 3 ^ 9 * m + 10084 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16782.1, data_15_16782.2]

/-- Complete interval computation for depth 15, residue 16783. -/
theorem bounds_15_16783 : exactInterval 15 16783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16783 : oddCount 16783 15 = 9 ∧ acceleratedOrbit 15 16783 = 10084 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16783) = 3 ^ 9 * m + 10084 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16783.1, data_15_16783.2]

/-- Complete interval computation for depth 15, residue 16784. -/
theorem bounds_15_16784 : exactInterval 15 16784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16784 : oddCount 16784 15 = 7 ∧ acceleratedOrbit 15 16784 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16784) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16784.1, data_15_16784.2]

/-- Complete interval computation for depth 15, residue 16785. -/
theorem bounds_15_16785 : exactInterval 15 16785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16785 : oddCount 16785 15 = 5 ∧ acceleratedOrbit 15 16785 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16785) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16785.1, data_15_16785.2]

/-- Complete interval computation for depth 15, residue 16786. -/
theorem bounds_15_16786 : exactInterval 15 16786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16786 : oddCount 16786 15 = 5 ∧ acceleratedOrbit 15 16786 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16786) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16786.1, data_15_16786.2]

/-- Complete interval computation for depth 15, residue 16787. -/
theorem bounds_15_16787 : exactInterval 15 16787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16787 : oddCount 16787 15 = 5 ∧ acceleratedOrbit 15 16787 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16787) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16787.1, data_15_16787.2]

/-- Complete interval computation for depth 15, residue 16788. -/
theorem bounds_15_16788 : exactInterval 15 16788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16788 : oddCount 16788 15 = 7 ∧ acceleratedOrbit 15 16788 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16788) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16788.1, data_15_16788.2]

/-- Complete interval computation for depth 15, residue 16789. -/
theorem bounds_15_16789 : exactInterval 15 16789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16789 : oddCount 16789 15 = 7 ∧ acceleratedOrbit 15 16789 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16789) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16789.1, data_15_16789.2]

/-- Complete interval computation for depth 15, residue 16790. -/
theorem bounds_15_16790 : exactInterval 15 16790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16790 : oddCount 16790 15 = 8 ∧ acceleratedOrbit 15 16790 = 3365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16790) = 3 ^ 8 * m + 3365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16790.1, data_15_16790.2]

/-- Complete interval computation for depth 15, residue 16791. -/
theorem bounds_15_16791 : exactInterval 15 16791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16791 : oddCount 16791 15 = 8 ∧ acceleratedOrbit 15 16791 = 3365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16791) = 3 ^ 8 * m + 3365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16791.1, data_15_16791.2]

/-- Complete interval computation for depth 15, residue 16792. -/
theorem bounds_15_16792 : exactInterval 15 16792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16792 : oddCount 16792 15 = 7 ∧ acceleratedOrbit 15 16792 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16792) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16792.1, data_15_16792.2]

/-- Complete interval computation for depth 15, residue 16793. -/
theorem bounds_15_16793 : exactInterval 15 16793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16793 : oddCount 16793 15 = 8 ∧ acceleratedOrbit 15 16793 = 3365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16793) = 3 ^ 8 * m + 3365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16793.1, data_15_16793.2]

/-- Complete interval computation for depth 15, residue 16794. -/
theorem bounds_15_16794 : exactInterval 15 16794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16794 : oddCount 16794 15 = 7 ∧ acceleratedOrbit 15 16794 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16794) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16794.1, data_15_16794.2]

/-- Complete interval computation for depth 15, residue 16795. -/
theorem bounds_15_16795 : exactInterval 15 16795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16795 : oddCount 16795 15 = 10 ∧ acceleratedOrbit 15 16795 = 30269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16795) = 3 ^ 10 * m + 30269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16795.1, data_15_16795.2]

/-- Complete interval computation for depth 15, residue 16796. -/
theorem bounds_15_16796 : exactInterval 15 16796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16796 : oddCount 16796 15 = 8 ∧ acceleratedOrbit 15 16796 = 3364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16796) = 3 ^ 8 * m + 3364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16796.1, data_15_16796.2]

/-- Complete interval computation for depth 15, residue 16797. -/
theorem bounds_15_16797 : exactInterval 15 16797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16797 : oddCount 16797 15 = 8 ∧ acceleratedOrbit 15 16797 = 3364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16797) = 3 ^ 8 * m + 3364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16797.1, data_15_16797.2]

/-- Complete interval computation for depth 15, residue 16798. -/
theorem bounds_15_16798 : exactInterval 15 16798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16798 : oddCount 16798 15 = 8 ∧ acceleratedOrbit 15 16798 = 3364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16798) = 3 ^ 8 * m + 3364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16798.1, data_15_16798.2]

/-- Complete interval computation for depth 15, residue 16799. -/
theorem bounds_15_16799 : exactInterval 15 16799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16799 : oddCount 16799 15 = 10 ∧ acceleratedOrbit 15 16799 = 30275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16799) = 3 ^ 10 * m + 30275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16799.1, data_15_16799.2]

/-- Complete interval computation for depth 15, residue 16800. -/
theorem bounds_15_16800 : exactInterval 15 16800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16800 : oddCount 16800 15 = 3 ∧ acceleratedOrbit 15 16800 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16800) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16800.1, data_15_16800.2]

/-- Complete interval computation for depth 15, residue 16801. -/
theorem bounds_15_16801 : exactInterval 15 16801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16801 : oddCount 16801 15 = 10 ∧ acceleratedOrbit 15 16801 = 30284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16801) = 3 ^ 10 * m + 30284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16801.1, data_15_16801.2]

/-- Complete interval computation for depth 15, residue 16802. -/
theorem bounds_15_16802 : exactInterval 15 16802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16802 : oddCount 16802 15 = 6 ∧ acceleratedOrbit 15 16802 = 374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16802) = 3 ^ 6 * m + 374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16802.1, data_15_16802.2]

/-- Complete interval computation for depth 15, residue 16803. -/
theorem bounds_15_16803 : exactInterval 15 16803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16803 : oddCount 16803 15 = 6 ∧ acceleratedOrbit 15 16803 = 374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16803) = 3 ^ 6 * m + 374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16803.1, data_15_16803.2]

/-- Complete interval computation for depth 15, residue 16804. -/
theorem bounds_15_16804 : exactInterval 15 16804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16804 : oddCount 16804 15 = 6 ∧ acceleratedOrbit 15 16804 = 374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16804) = 3 ^ 6 * m + 374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16804.1, data_15_16804.2]

/-- Complete interval computation for depth 15, residue 16805. -/
theorem bounds_15_16805 : exactInterval 15 16805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16805 : oddCount 16805 15 = 6 ∧ acceleratedOrbit 15 16805 = 374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16805) = 3 ^ 6 * m + 374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16805.1, data_15_16805.2]

/-- Complete interval computation for depth 15, residue 16806. -/
theorem bounds_15_16806 : exactInterval 15 16806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16806 : oddCount 16806 15 = 6 ∧ acceleratedOrbit 15 16806 = 374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16806) = 3 ^ 6 * m + 374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16806.1, data_15_16806.2]

/-- Complete interval computation for depth 15, residue 16807. -/
theorem bounds_15_16807 : exactInterval 15 16807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16807 : oddCount 16807 15 = 10 ∧ acceleratedOrbit 15 16807 = 30293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16807) = 3 ^ 10 * m + 30293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16807.1, data_15_16807.2]

/-- Complete interval computation for depth 15, residue 16808. -/
theorem bounds_15_16808 : exactInterval 15 16808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16808 : oddCount 16808 15 = 3 ∧ acceleratedOrbit 15 16808 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16808) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16808.1, data_15_16808.2]

end Collatz.Research.PassageAtlas.Batch0513
