import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0849

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27787. -/
theorem bounds_15_27787 : exactInterval 15 27787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27787 : oddCount 27787 15 = 7 ∧ acceleratedOrbit 15 27787 = 1855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27787) = 3 ^ 7 * m + 1855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27787.1, data_15_27787.2]

/-- Complete interval computation for depth 15, residue 27788. -/
theorem bounds_15_27788 : exactInterval 15 27788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27788 : oddCount 27788 15 = 6 ∧ acceleratedOrbit 15 27788 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27788) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27788.1, data_15_27788.2]

/-- Complete interval computation for depth 15, residue 27789. -/
theorem bounds_15_27789 : exactInterval 15 27789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27789 : oddCount 27789 15 = 6 ∧ acceleratedOrbit 15 27789 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27789) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27789.1, data_15_27789.2]

/-- Complete interval computation for depth 15, residue 27790. -/
theorem bounds_15_27790 : exactInterval 15 27790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27790 : oddCount 27790 15 = 7 ∧ acceleratedOrbit 15 27790 = 1855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27790) = 3 ^ 7 * m + 1855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27790.1, data_15_27790.2]

/-- Complete interval computation for depth 15, residue 27791. -/
theorem bounds_15_27791 : exactInterval 15 27791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27791 : oddCount 27791 15 = 7 ∧ acceleratedOrbit 15 27791 = 1855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27791) = 3 ^ 7 * m + 1855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27791.1, data_15_27791.2]

/-- Complete interval computation for depth 15, residue 27792. -/
theorem bounds_15_27792 : exactInterval 15 27792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27792 : oddCount 27792 15 = 6 ∧ acceleratedOrbit 15 27792 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27792) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27792.1, data_15_27792.2]

/-- Complete interval computation for depth 15, residue 27793. -/
theorem bounds_15_27793 : exactInterval 15 27793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27793 : oddCount 27793 15 = 9 ∧ acceleratedOrbit 15 27793 = 16699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27793) = 3 ^ 9 * m + 16699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27793.1, data_15_27793.2]

/-- Complete interval computation for depth 15, residue 27794. -/
theorem bounds_15_27794 : exactInterval 15 27794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27794 : oddCount 27794 15 = 9 ∧ acceleratedOrbit 15 27794 = 16699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27794) = 3 ^ 9 * m + 16699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27794.1, data_15_27794.2]

/-- Complete interval computation for depth 15, residue 27795. -/
theorem bounds_15_27795 : exactInterval 15 27795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27795 : oddCount 27795 15 = 9 ∧ acceleratedOrbit 15 27795 = 16699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27795) = 3 ^ 9 * m + 16699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27795.1, data_15_27795.2]

/-- Complete interval computation for depth 15, residue 27796. -/
theorem bounds_15_27796 : exactInterval 15 27796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27796 : oddCount 27796 15 = 6 ∧ acceleratedOrbit 15 27796 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27796) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27796.1, data_15_27796.2]

/-- Complete interval computation for depth 15, residue 27797. -/
theorem bounds_15_27797 : exactInterval 15 27797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27797 : oddCount 27797 15 = 6 ∧ acceleratedOrbit 15 27797 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27797) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27797.1, data_15_27797.2]

/-- Complete interval computation for depth 15, residue 27798. -/
theorem bounds_15_27798 : exactInterval 15 27798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27798 : oddCount 27798 15 = 6 ∧ acceleratedOrbit 15 27798 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27798) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27798.1, data_15_27798.2]

/-- Complete interval computation for depth 15, residue 27799. -/
theorem bounds_15_27799 : exactInterval 15 27799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27799 : oddCount 27799 15 = 6 ∧ acceleratedOrbit 15 27799 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27799) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27799.1, data_15_27799.2]

/-- Complete interval computation for depth 15, residue 27800. -/
theorem bounds_15_27800 : exactInterval 15 27800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27800 : oddCount 27800 15 = 6 ∧ acceleratedOrbit 15 27800 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27800) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27800.1, data_15_27800.2]

/-- Complete interval computation for depth 15, residue 27801. -/
theorem bounds_15_27801 : exactInterval 15 27801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27801 : oddCount 27801 15 = 7 ∧ acceleratedOrbit 15 27801 = 1856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27801) = 3 ^ 7 * m + 1856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27801.1, data_15_27801.2]

/-- Complete interval computation for depth 15, residue 27802. -/
theorem bounds_15_27802 : exactInterval 15 27802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27802 : oddCount 27802 15 = 6 ∧ acceleratedOrbit 15 27802 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27802) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27802.1, data_15_27802.2]

/-- Complete interval computation for depth 15, residue 27803. -/
theorem bounds_15_27803 : exactInterval 15 27803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27803 : oddCount 27803 15 = 10 ∧ acceleratedOrbit 15 27803 = 50105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27803) = 3 ^ 10 * m + 50105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27803.1, data_15_27803.2]

/-- Complete interval computation for depth 15, residue 27804. -/
theorem bounds_15_27804 : exactInterval 15 27804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27804 : oddCount 27804 15 = 9 ∧ acceleratedOrbit 15 27804 = 16706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27804) = 3 ^ 9 * m + 16706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27804.1, data_15_27804.2]

/-- Complete interval computation for depth 15, residue 27805. -/
theorem bounds_15_27805 : exactInterval 15 27805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27805 : oddCount 27805 15 = 9 ∧ acceleratedOrbit 15 27805 = 16706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27805) = 3 ^ 9 * m + 16706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27805.1, data_15_27805.2]

/-- Complete interval computation for depth 15, residue 27806. -/
theorem bounds_15_27806 : exactInterval 15 27806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27806 : oddCount 27806 15 = 9 ∧ acceleratedOrbit 15 27806 = 16706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27806) = 3 ^ 9 * m + 16706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27806.1, data_15_27806.2]

/-- Complete interval computation for depth 15, residue 27807. -/
theorem bounds_15_27807 : exactInterval 15 27807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27807 : oddCount 27807 15 = 12 ∧ acceleratedOrbit 15 27807 = 451001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27807) = 3 ^ 12 * m + 451001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27807.1, data_15_27807.2]

/-- Complete interval computation for depth 15, residue 27808. -/
theorem bounds_15_27808 : exactInterval 15 27808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27808 : oddCount 27808 15 = 3 ∧ acceleratedOrbit 15 27808 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27808) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27808.1, data_15_27808.2]

/-- Complete interval computation for depth 15, residue 27809. -/
theorem bounds_15_27809 : exactInterval 15 27809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27809 : oddCount 27809 15 = 11 ∧ acceleratedOrbit 15 27809 = 150356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27809) = 3 ^ 11 * m + 150356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27809.1, data_15_27809.2]

/-- Complete interval computation for depth 15, residue 27810. -/
theorem bounds_15_27810 : exactInterval 15 27810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27810 : oddCount 27810 15 = 9 ∧ acceleratedOrbit 15 27810 = 16712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27810) = 3 ^ 9 * m + 16712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27810.1, data_15_27810.2]

/-- Complete interval computation for depth 15, residue 27811. -/
theorem bounds_15_27811 : exactInterval 15 27811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27811 : oddCount 27811 15 = 9 ∧ acceleratedOrbit 15 27811 = 16712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27811) = 3 ^ 9 * m + 16712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27811.1, data_15_27811.2]

/-- Complete interval computation for depth 15, residue 27812. -/
theorem bounds_15_27812 : exactInterval 15 27812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27812 : oddCount 27812 15 = 9 ∧ acceleratedOrbit 15 27812 = 16712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27812) = 3 ^ 9 * m + 16712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27812.1, data_15_27812.2]

/-- Complete interval computation for depth 15, residue 27813. -/
theorem bounds_15_27813 : exactInterval 15 27813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27813 : oddCount 27813 15 = 9 ∧ acceleratedOrbit 15 27813 = 16712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27813) = 3 ^ 9 * m + 16712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27813.1, data_15_27813.2]

/-- Complete interval computation for depth 15, residue 27814. -/
theorem bounds_15_27814 : exactInterval 15 27814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27814 : oddCount 27814 15 = 9 ∧ acceleratedOrbit 15 27814 = 16712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27814) = 3 ^ 9 * m + 16712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27814.1, data_15_27814.2]

/-- Complete interval computation for depth 15, residue 27815. -/
theorem bounds_15_27815 : exactInterval 15 27815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27815 : oddCount 27815 15 = 11 ∧ acceleratedOrbit 15 27815 = 150380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27815) = 3 ^ 11 * m + 150380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27815.1, data_15_27815.2]

/-- Complete interval computation for depth 15, residue 27816. -/
theorem bounds_15_27816 : exactInterval 15 27816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27816 : oddCount 27816 15 = 3 ∧ acceleratedOrbit 15 27816 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27816) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27816.1, data_15_27816.2]

/-- Complete interval computation for depth 15, residue 27817. -/
theorem bounds_15_27817 : exactInterval 15 27817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27817 : oddCount 27817 15 = 8 ∧ acceleratedOrbit 15 27817 = 5570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27817) = 3 ^ 8 * m + 5570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27817.1, data_15_27817.2]

/-- Complete interval computation for depth 15, residue 27818. -/
theorem bounds_15_27818 : exactInterval 15 27818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27818 : oddCount 27818 15 = 3 ∧ acceleratedOrbit 15 27818 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27818) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27818.1, data_15_27818.2]

/-- Complete interval computation for depth 15, residue 27819. -/
theorem bounds_15_27819 : exactInterval 15 27819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27819 : oddCount 27819 15 = 6 ∧ acceleratedOrbit 15 27819 = 619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27819) = 3 ^ 6 * m + 619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27819.1, data_15_27819.2]

end Collatz.Research.PassageAtlas.Batch0849
