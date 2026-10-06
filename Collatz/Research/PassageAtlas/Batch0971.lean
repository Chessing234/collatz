import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0971

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31784. -/
theorem bounds_15_31784 : exactInterval 15 31784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31784 : oddCount 31784 15 = 7 ∧ acceleratedOrbit 15 31784 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31784) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31784.1, data_15_31784.2]

/-- Complete interval computation for depth 15, residue 31785. -/
theorem bounds_15_31785 : exactInterval 15 31785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31785 : oddCount 31785 15 = 8 ∧ acceleratedOrbit 15 31785 = 6365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31785) = 3 ^ 8 * m + 6365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31785.1, data_15_31785.2]

/-- Complete interval computation for depth 15, residue 31786. -/
theorem bounds_15_31786 : exactInterval 15 31786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31786 : oddCount 31786 15 = 7 ∧ acceleratedOrbit 15 31786 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31786) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31786.1, data_15_31786.2]

/-- Complete interval computation for depth 15, residue 31787. -/
theorem bounds_15_31787 : exactInterval 15 31787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31787 : oddCount 31787 15 = 7 ∧ acceleratedOrbit 15 31787 = 2123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31787) = 3 ^ 7 * m + 2123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31787.1, data_15_31787.2]

/-- Complete interval computation for depth 15, residue 31788. -/
theorem bounds_15_31788 : exactInterval 15 31788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31788 : oddCount 31788 15 = 7 ∧ acceleratedOrbit 15 31788 = 2123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31788) = 3 ^ 7 * m + 2123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31788.1, data_15_31788.2]

/-- Complete interval computation for depth 15, residue 31789. -/
theorem bounds_15_31789 : exactInterval 15 31789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31789 : oddCount 31789 15 = 7 ∧ acceleratedOrbit 15 31789 = 2123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31789) = 3 ^ 7 * m + 2123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31789.1, data_15_31789.2]

/-- Complete interval computation for depth 15, residue 31790. -/
theorem bounds_15_31790 : exactInterval 15 31790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31790 : oddCount 31790 15 = 7 ∧ acceleratedOrbit 15 31790 = 2123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31790) = 3 ^ 7 * m + 2123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31790.1, data_15_31790.2]

/-- Complete interval computation for depth 15, residue 31791. -/
theorem bounds_15_31791 : exactInterval 15 31791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31791 : oddCount 31791 15 = 10 ∧ acceleratedOrbit 15 31791 = 57293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31791) = 3 ^ 10 * m + 57293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31791.1, data_15_31791.2]

/-- Complete interval computation for depth 15, residue 31792. -/
theorem bounds_15_31792 : exactInterval 15 31792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31792 : oddCount 31792 15 = 7 ∧ acceleratedOrbit 15 31792 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31792) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31792.1, data_15_31792.2]

/-- Complete interval computation for depth 15, residue 31793. -/
theorem bounds_15_31793 : exactInterval 15 31793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31793 : oddCount 31793 15 = 7 ∧ acceleratedOrbit 15 31793 = 2123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31793) = 3 ^ 7 * m + 2123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31793.1, data_15_31793.2]

/-- Complete interval computation for depth 15, residue 31794. -/
theorem bounds_15_31794 : exactInterval 15 31794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31794 : oddCount 31794 15 = 7 ∧ acceleratedOrbit 15 31794 = 2123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31794) = 3 ^ 7 * m + 2123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31794.1, data_15_31794.2]

/-- Complete interval computation for depth 15, residue 31795. -/
theorem bounds_15_31795 : exactInterval 15 31795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31795 : oddCount 31795 15 = 7 ∧ acceleratedOrbit 15 31795 = 2123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31795) = 3 ^ 7 * m + 2123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31795.1, data_15_31795.2]

/-- Complete interval computation for depth 15, residue 31796. -/
theorem bounds_15_31796 : exactInterval 15 31796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31796 : oddCount 31796 15 = 7 ∧ acceleratedOrbit 15 31796 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31796) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31796.1, data_15_31796.2]

/-- Complete interval computation for depth 15, residue 31797. -/
theorem bounds_15_31797 : exactInterval 15 31797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31797 : oddCount 31797 15 = 7 ∧ acceleratedOrbit 15 31797 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31797) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31797.1, data_15_31797.2]

/-- Complete interval computation for depth 15, residue 31798. -/
theorem bounds_15_31798 : exactInterval 15 31798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31798 : oddCount 31798 15 = 10 ∧ acceleratedOrbit 15 31798 = 57307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31798) = 3 ^ 10 * m + 57307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31798.1, data_15_31798.2]

/-- Complete interval computation for depth 15, residue 31799. -/
theorem bounds_15_31799 : exactInterval 15 31799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31799 : oddCount 31799 15 = 10 ∧ acceleratedOrbit 15 31799 = 57307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31799) = 3 ^ 10 * m + 57307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31799.1, data_15_31799.2]

/-- Complete interval computation for depth 15, residue 31800. -/
theorem bounds_15_31800 : exactInterval 15 31800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31800 : oddCount 31800 15 = 5 ∧ acceleratedOrbit 15 31800 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31800) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31800.1, data_15_31800.2]

/-- Complete interval computation for depth 15, residue 31801. -/
theorem bounds_15_31801 : exactInterval 15 31801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31801 : oddCount 31801 15 = 9 ∧ acceleratedOrbit 15 31801 = 19106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31801) = 3 ^ 9 * m + 19106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31801.1, data_15_31801.2]

/-- Complete interval computation for depth 15, residue 31802. -/
theorem bounds_15_31802 : exactInterval 15 31802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31802 : oddCount 31802 15 = 5 ∧ acceleratedOrbit 15 31802 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31802) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31802.1, data_15_31802.2]

/-- Complete interval computation for depth 15, residue 31803. -/
theorem bounds_15_31803 : exactInterval 15 31803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31803 : oddCount 31803 15 = 9 ∧ acceleratedOrbit 15 31803 = 19106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31803) = 3 ^ 9 * m + 19106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31803.1, data_15_31803.2]

/-- Complete interval computation for depth 15, residue 31804. -/
theorem bounds_15_31804 : exactInterval 15 31804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31804 : oddCount 31804 15 = 5 ∧ acceleratedOrbit 15 31804 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31804) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31804.1, data_15_31804.2]

/-- Complete interval computation for depth 15, residue 31805. -/
theorem bounds_15_31805 : exactInterval 15 31805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31805 : oddCount 31805 15 = 5 ∧ acceleratedOrbit 15 31805 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31805) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31805.1, data_15_31805.2]

/-- Complete interval computation for depth 15, residue 31806. -/
theorem bounds_15_31806 : exactInterval 15 31806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31806 : oddCount 31806 15 = 11 ∧ acceleratedOrbit 15 31806 = 171962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31806) = 3 ^ 11 * m + 171962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31806.1, data_15_31806.2]

/-- Complete interval computation for depth 15, residue 31807. -/
theorem bounds_15_31807 : exactInterval 15 31807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31807 : oddCount 31807 15 = 11 ∧ acceleratedOrbit 15 31807 = 171962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31807) = 3 ^ 11 * m + 171962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31807.1, data_15_31807.2]

/-- Complete interval computation for depth 15, residue 31808. -/
theorem bounds_15_31808 : exactInterval 15 31808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31808 : oddCount 31808 15 = 4 ∧ acceleratedOrbit 15 31808 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31808) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31808.1, data_15_31808.2]

/-- Complete interval computation for depth 15, residue 31809. -/
theorem bounds_15_31809 : exactInterval 15 31809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31809 : oddCount 31809 15 = 9 ∧ acceleratedOrbit 15 31809 = 19115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31809) = 3 ^ 9 * m + 19115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31809.1, data_15_31809.2]

/-- Complete interval computation for depth 15, residue 31810. -/
theorem bounds_15_31810 : exactInterval 15 31810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31810 : oddCount 31810 15 = 9 ∧ acceleratedOrbit 15 31810 = 19115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31810) = 3 ^ 9 * m + 19115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31810.1, data_15_31810.2]

/-- Complete interval computation for depth 15, residue 31811. -/
theorem bounds_15_31811 : exactInterval 15 31811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31811 : oddCount 31811 15 = 9 ∧ acceleratedOrbit 15 31811 = 19115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31811) = 3 ^ 9 * m + 19115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31811.1, data_15_31811.2]

/-- Complete interval computation for depth 15, residue 31812. -/
theorem bounds_15_31812 : exactInterval 15 31812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31812 : oddCount 31812 15 = 7 ∧ acceleratedOrbit 15 31812 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31812) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31812.1, data_15_31812.2]

/-- Complete interval computation for depth 15, residue 31813. -/
theorem bounds_15_31813 : exactInterval 15 31813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31813 : oddCount 31813 15 = 7 ∧ acceleratedOrbit 15 31813 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31813) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31813.1, data_15_31813.2]

/-- Complete interval computation for depth 15, residue 31814. -/
theorem bounds_15_31814 : exactInterval 15 31814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31814 : oddCount 31814 15 = 7 ∧ acceleratedOrbit 15 31814 = 2126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31814) = 3 ^ 7 * m + 2126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31814.1, data_15_31814.2]

/-- Complete interval computation for depth 15, residue 31815. -/
theorem bounds_15_31815 : exactInterval 15 31815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31815 : oddCount 31815 15 = 8 ∧ acceleratedOrbit 15 31815 = 6371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31815) = 3 ^ 8 * m + 6371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31815.1, data_15_31815.2]

/-- Complete interval computation for depth 15, residue 31816. -/
theorem bounds_15_31816 : exactInterval 15 31816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31816 : oddCount 31816 15 = 8 ∧ acceleratedOrbit 15 31816 = 6374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31816) = 3 ^ 8 * m + 6374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31816.1, data_15_31816.2]

end Collatz.Research.PassageAtlas.Batch0971
