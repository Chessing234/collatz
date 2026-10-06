import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0666

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21790. -/
theorem bounds_15_21790 : exactInterval 15 21790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21790 : oddCount 21790 15 = 10 ∧ acceleratedOrbit 15 21790 = 39275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21790) = 3 ^ 10 * m + 39275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21790.1, data_15_21790.2]

/-- Complete interval computation for depth 15, residue 21791. -/
theorem bounds_15_21791 : exactInterval 15 21791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21791 : oddCount 21791 15 = 8 ∧ acceleratedOrbit 15 21791 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21791) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21791.1, data_15_21791.2]

/-- Complete interval computation for depth 15, residue 21792. -/
theorem bounds_15_21792 : exactInterval 15 21792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21792 : oddCount 21792 15 = 9 ∧ acceleratedOrbit 15 21792 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21792) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21792.1, data_15_21792.2]

/-- Complete interval computation for depth 15, residue 21793. -/
theorem bounds_15_21793 : exactInterval 15 21793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21793 : oddCount 21793 15 = 7 ∧ acceleratedOrbit 15 21793 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21793) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21793.1, data_15_21793.2]

/-- Complete interval computation for depth 15, residue 21794. -/
theorem bounds_15_21794 : exactInterval 15 21794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21794 : oddCount 21794 15 = 8 ∧ acceleratedOrbit 15 21794 = 4367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21794) = 3 ^ 8 * m + 4367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21794.1, data_15_21794.2]

/-- Complete interval computation for depth 15, residue 21795. -/
theorem bounds_15_21795 : exactInterval 15 21795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21795 : oddCount 21795 15 = 8 ∧ acceleratedOrbit 15 21795 = 4367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21795) = 3 ^ 8 * m + 4367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21795.1, data_15_21795.2]

/-- Complete interval computation for depth 15, residue 21796. -/
theorem bounds_15_21796 : exactInterval 15 21796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21796 : oddCount 21796 15 = 8 ∧ acceleratedOrbit 15 21796 = 4367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21796) = 3 ^ 8 * m + 4367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21796.1, data_15_21796.2]

/-- Complete interval computation for depth 15, residue 21797. -/
theorem bounds_15_21797 : exactInterval 15 21797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21797 : oddCount 21797 15 = 8 ∧ acceleratedOrbit 15 21797 = 4367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21797) = 3 ^ 8 * m + 4367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21797.1, data_15_21797.2]

/-- Complete interval computation for depth 15, residue 21798. -/
theorem bounds_15_21798 : exactInterval 15 21798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21798 : oddCount 21798 15 = 8 ∧ acceleratedOrbit 15 21798 = 4367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21798) = 3 ^ 8 * m + 4367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21798.1, data_15_21798.2]

/-- Complete interval computation for depth 15, residue 21799. -/
theorem bounds_15_21799 : exactInterval 15 21799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21799 : oddCount 21799 15 = 6 ∧ acceleratedOrbit 15 21799 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21799) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21799.1, data_15_21799.2]

/-- Complete interval computation for depth 15, residue 21800. -/
theorem bounds_15_21800 : exactInterval 15 21800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21800 : oddCount 21800 15 = 9 ∧ acceleratedOrbit 15 21800 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21800) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21800.1, data_15_21800.2]

/-- Complete interval computation for depth 15, residue 21801. -/
theorem bounds_15_21801 : exactInterval 15 21801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21801 : oddCount 21801 15 = 9 ∧ acceleratedOrbit 15 21801 = 13097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21801) = 3 ^ 9 * m + 13097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21801.1, data_15_21801.2]

/-- Complete interval computation for depth 15, residue 21802. -/
theorem bounds_15_21802 : exactInterval 15 21802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21802 : oddCount 21802 15 = 9 ∧ acceleratedOrbit 15 21802 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21802) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21802.1, data_15_21802.2]

/-- Complete interval computation for depth 15, residue 21803. -/
theorem bounds_15_21803 : exactInterval 15 21803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21803 : oddCount 21803 15 = 8 ∧ acceleratedOrbit 15 21803 = 4367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21803) = 3 ^ 8 * m + 4367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21803.1, data_15_21803.2]

/-- Complete interval computation for depth 15, residue 21804. -/
theorem bounds_15_21804 : exactInterval 15 21804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21804 : oddCount 21804 15 = 8 ∧ acceleratedOrbit 15 21804 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21804) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21804.1, data_15_21804.2]

/-- Complete interval computation for depth 15, residue 21805. -/
theorem bounds_15_21805 : exactInterval 15 21805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21805 : oddCount 21805 15 = 8 ∧ acceleratedOrbit 15 21805 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21805) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21805.1, data_15_21805.2]

/-- Complete interval computation for depth 15, residue 21806. -/
theorem bounds_15_21806 : exactInterval 15 21806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21806 : oddCount 21806 15 = 8 ∧ acceleratedOrbit 15 21806 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21806) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21806.1, data_15_21806.2]

/-- Complete interval computation for depth 15, residue 21807. -/
theorem bounds_15_21807 : exactInterval 15 21807 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21807) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21807 : oddCount 21807 15 = 9 ∧ acceleratedOrbit 15 21807 = 13100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21807) = 3 ^ 9 * m + 13100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21807.1, data_15_21807.2]

/-- Complete interval computation for depth 15, residue 21808. -/
theorem bounds_15_21808 : exactInterval 15 21808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21808 : oddCount 21808 15 = 9 ∧ acceleratedOrbit 15 21808 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21808) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21808.1, data_15_21808.2]

/-- Complete interval computation for depth 15, residue 21809. -/
theorem bounds_15_21809 : exactInterval 15 21809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21809 : oddCount 21809 15 = 8 ∧ acceleratedOrbit 15 21809 = 4369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21809) = 3 ^ 8 * m + 4369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21809.1, data_15_21809.2]

/-- Complete interval computation for depth 15, residue 21810. -/
theorem bounds_15_21810 : exactInterval 15 21810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21810 : oddCount 21810 15 = 8 ∧ acceleratedOrbit 15 21810 = 4369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21810) = 3 ^ 8 * m + 4369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21810.1, data_15_21810.2]

/-- Complete interval computation for depth 15, residue 21811. -/
theorem bounds_15_21811 : exactInterval 15 21811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21811 : oddCount 21811 15 = 8 ∧ acceleratedOrbit 15 21811 = 4369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21811) = 3 ^ 8 * m + 4369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21811.1, data_15_21811.2]

/-- Complete interval computation for depth 15, residue 21812. -/
theorem bounds_15_21812 : exactInterval 15 21812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21812 : oddCount 21812 15 = 9 ∧ acceleratedOrbit 15 21812 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21812) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21812.1, data_15_21812.2]

/-- Complete interval computation for depth 15, residue 21813. -/
theorem bounds_15_21813 : exactInterval 15 21813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21813 : oddCount 21813 15 = 9 ∧ acceleratedOrbit 15 21813 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21813) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21813.1, data_15_21813.2]

/-- Complete interval computation for depth 15, residue 21814. -/
theorem bounds_15_21814 : exactInterval 15 21814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21814 : oddCount 21814 15 = 9 ∧ acceleratedOrbit 15 21814 = 13105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21814) = 3 ^ 9 * m + 13105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21814.1, data_15_21814.2]

/-- Complete interval computation for depth 15, residue 21815. -/
theorem bounds_15_21815 : exactInterval 15 21815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21815 : oddCount 21815 15 = 9 ∧ acceleratedOrbit 15 21815 = 13105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21815) = 3 ^ 9 * m + 13105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21815.1, data_15_21815.2]

/-- Complete interval computation for depth 15, residue 21816. -/
theorem bounds_15_21816 : exactInterval 15 21816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21816 : oddCount 21816 15 = 9 ∧ acceleratedOrbit 15 21816 = 13112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21816) = 3 ^ 9 * m + 13112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21816.1, data_15_21816.2]

/-- Complete interval computation for depth 15, residue 21817. -/
theorem bounds_15_21817 : exactInterval 15 21817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21817 : oddCount 21817 15 = 11 ∧ acceleratedOrbit 15 21817 = 117962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21817) = 3 ^ 11 * m + 117962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21817.1, data_15_21817.2]

/-- Complete interval computation for depth 15, residue 21818. -/
theorem bounds_15_21818 : exactInterval 15 21818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21818 : oddCount 21818 15 = 9 ∧ acceleratedOrbit 15 21818 = 13112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21818) = 3 ^ 9 * m + 13112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21818.1, data_15_21818.2]

/-- Complete interval computation for depth 15, residue 21819. -/
theorem bounds_15_21819 : exactInterval 15 21819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21819 : oddCount 21819 15 = 8 ∧ acceleratedOrbit 15 21819 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21819) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21819.1, data_15_21819.2]

/-- Complete interval computation for depth 15, residue 21820. -/
theorem bounds_15_21820 : exactInterval 15 21820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21820 : oddCount 21820 15 = 9 ∧ acceleratedOrbit 15 21820 = 13112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21820) = 3 ^ 9 * m + 13112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21820.1, data_15_21820.2]

/-- Complete interval computation for depth 15, residue 21821. -/
theorem bounds_15_21821 : exactInterval 15 21821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21821 : oddCount 21821 15 = 9 ∧ acceleratedOrbit 15 21821 = 13112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21821) = 3 ^ 9 * m + 13112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21821.1, data_15_21821.2]

/-- Complete interval computation for depth 15, residue 21822. -/
theorem bounds_15_21822 : exactInterval 15 21822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21822 : oddCount 21822 15 = 10 ∧ acceleratedOrbit 15 21822 = 39329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21822) = 3 ^ 10 * m + 39329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21822.1, data_15_21822.2]

end Collatz.Research.PassageAtlas.Batch0666
