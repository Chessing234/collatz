import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0025

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 786. -/
theorem bounds_15_786 : exactInterval 15 786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_786 : oddCount 786 15 = 9 ∧ acceleratedOrbit 15 786 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 786) = 3 ^ 9 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_786.1, data_15_786.2]

/-- Complete interval computation for depth 15, residue 787. -/
theorem bounds_15_787 : exactInterval 15 787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_787 : oddCount 787 15 = 9 ∧ acceleratedOrbit 15 787 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 787) = 3 ^ 9 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_787.1, data_15_787.2]

/-- Complete interval computation for depth 15, residue 788. -/
theorem bounds_15_788 : exactInterval 15 788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_788 : oddCount 788 15 = 6 ∧ acceleratedOrbit 15 788 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 788) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_788.1, data_15_788.2]

/-- Complete interval computation for depth 15, residue 789. -/
theorem bounds_15_789 : exactInterval 15 789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_789 : oddCount 789 15 = 6 ∧ acceleratedOrbit 15 789 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 789) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_789.1, data_15_789.2]

/-- Complete interval computation for depth 15, residue 790. -/
theorem bounds_15_790 : exactInterval 15 790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_790 : oddCount 790 15 = 9 ∧ acceleratedOrbit 15 790 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 790) = 3 ^ 9 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_790.1, data_15_790.2]

/-- Complete interval computation for depth 15, residue 791. -/
theorem bounds_15_791 : exactInterval 15 791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_791 : oddCount 791 15 = 9 ∧ acceleratedOrbit 15 791 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 791) = 3 ^ 9 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_791.1, data_15_791.2]

/-- Complete interval computation for depth 15, residue 792. -/
theorem bounds_15_792 : exactInterval 15 792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_792 : oddCount 792 15 = 6 ∧ acceleratedOrbit 15 792 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 792) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_792.1, data_15_792.2]

/-- Complete interval computation for depth 15, residue 793. -/
theorem bounds_15_793 : exactInterval 15 793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_793 : oddCount 793 15 = 9 ∧ acceleratedOrbit 15 793 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 793) = 3 ^ 9 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_793.1, data_15_793.2]

/-- Complete interval computation for depth 15, residue 794. -/
theorem bounds_15_794 : exactInterval 15 794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_794 : oddCount 794 15 = 6 ∧ acceleratedOrbit 15 794 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 794) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_794.1, data_15_794.2]

/-- Complete interval computation for depth 15, residue 795. -/
theorem bounds_15_795 : exactInterval 15 795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_795 : oddCount 795 15 = 11 ∧ acceleratedOrbit 15 795 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 795) = 3 ^ 11 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_795.1, data_15_795.2]

/-- Complete interval computation for depth 15, residue 796. -/
theorem bounds_15_796 : exactInterval 15 796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_796 : oddCount 796 15 = 9 ∧ acceleratedOrbit 15 796 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 796) = 3 ^ 9 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_796.1, data_15_796.2]

/-- Complete interval computation for depth 15, residue 797. -/
theorem bounds_15_797 : exactInterval 15 797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_797 : oddCount 797 15 = 9 ∧ acceleratedOrbit 15 797 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 797) = 3 ^ 9 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_797.1, data_15_797.2]

/-- Complete interval computation for depth 15, residue 798. -/
theorem bounds_15_798 : exactInterval 15 798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_798 : oddCount 798 15 = 9 ∧ acceleratedOrbit 15 798 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 798) = 3 ^ 9 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_798.1, data_15_798.2]

/-- Complete interval computation for depth 15, residue 799. -/
theorem bounds_15_799 : exactInterval 15 799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_799 : oddCount 799 15 = 9 ∧ acceleratedOrbit 15 799 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 799) = 3 ^ 9 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_799.1, data_15_799.2]

/-- Complete interval computation for depth 15, residue 800. -/
theorem bounds_15_800 : exactInterval 15 800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_800 : oddCount 800 15 = 6 ∧ acceleratedOrbit 15 800 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 800) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_800.1, data_15_800.2]

/-- Complete interval computation for depth 15, residue 801. -/
theorem bounds_15_801 : exactInterval 15 801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_801 : oddCount 801 15 = 10 ∧ acceleratedOrbit 15 801 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 801) = 3 ^ 10 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_801.1, data_15_801.2]

/-- Complete interval computation for depth 15, residue 802. -/
theorem bounds_15_802 : exactInterval 15 802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_802 : oddCount 802 15 = 4 ∧ acceleratedOrbit 15 802 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 802) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_802.1, data_15_802.2]

/-- Complete interval computation for depth 15, residue 803. -/
theorem bounds_15_803 : exactInterval 15 803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_803 : oddCount 803 15 = 4 ∧ acceleratedOrbit 15 803 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 803) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_803.1, data_15_803.2]

/-- Complete interval computation for depth 15, residue 804. -/
theorem bounds_15_804 : exactInterval 15 804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_804 : oddCount 804 15 = 4 ∧ acceleratedOrbit 15 804 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 804) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_804.1, data_15_804.2]

/-- Complete interval computation for depth 15, residue 805. -/
theorem bounds_15_805 : exactInterval 15 805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_805 : oddCount 805 15 = 4 ∧ acceleratedOrbit 15 805 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 805) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_805.1, data_15_805.2]

/-- Complete interval computation for depth 15, residue 806. -/
theorem bounds_15_806 : exactInterval 15 806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_806 : oddCount 806 15 = 4 ∧ acceleratedOrbit 15 806 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 806) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_806.1, data_15_806.2]

/-- Complete interval computation for depth 15, residue 807. -/
theorem bounds_15_807 : exactInterval 15 807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_807 : oddCount 807 15 = 12 ∧ acceleratedOrbit 15 807 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 807) = 3 ^ 12 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_807.1, data_15_807.2]

/-- Complete interval computation for depth 15, residue 808. -/
theorem bounds_15_808 : exactInterval 15 808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_808 : oddCount 808 15 = 6 ∧ acceleratedOrbit 15 808 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 808) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_808.1, data_15_808.2]

/-- Complete interval computation for depth 15, residue 809. -/
theorem bounds_15_809 : exactInterval 15 809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_809 : oddCount 809 15 = 9 ∧ acceleratedOrbit 15 809 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 809) = 3 ^ 9 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_809.1, data_15_809.2]

/-- Complete interval computation for depth 15, residue 810. -/
theorem bounds_15_810 : exactInterval 15 810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_810 : oddCount 810 15 = 6 ∧ acceleratedOrbit 15 810 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 810) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_810.1, data_15_810.2]

/-- Complete interval computation for depth 15, residue 811. -/
theorem bounds_15_811 : exactInterval 15 811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_811 : oddCount 811 15 = 8 ∧ acceleratedOrbit 15 811 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 811) = 3 ^ 8 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_811.1, data_15_811.2]

/-- Complete interval computation for depth 15, residue 812. -/
theorem bounds_15_812 : exactInterval 15 812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_812 : oddCount 812 15 = 7 ∧ acceleratedOrbit 15 812 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 812) = 3 ^ 7 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_812.1, data_15_812.2]

/-- Complete interval computation for depth 15, residue 813. -/
theorem bounds_15_813 : exactInterval 15 813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_813 : oddCount 813 15 = 7 ∧ acceleratedOrbit 15 813 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 813) = 3 ^ 7 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_813.1, data_15_813.2]

/-- Complete interval computation for depth 15, residue 814. -/
theorem bounds_15_814 : exactInterval 15 814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_814 : oddCount 814 15 = 7 ∧ acceleratedOrbit 15 814 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 814) = 3 ^ 7 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_814.1, data_15_814.2]

/-- Complete interval computation for depth 15, residue 815. -/
theorem bounds_15_815 : exactInterval 15 815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_815 : oddCount 815 15 = 8 ∧ acceleratedOrbit 15 815 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 815) = 3 ^ 8 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_815.1, data_15_815.2]

/-- Complete interval computation for depth 15, residue 816. -/
theorem bounds_15_816 : exactInterval 15 816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_816 : oddCount 816 15 = 6 ∧ acceleratedOrbit 15 816 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 816) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_816.1, data_15_816.2]

/-- Complete interval computation for depth 15, residue 817. -/
theorem bounds_15_817 : exactInterval 15 817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_817 : oddCount 817 15 = 7 ∧ acceleratedOrbit 15 817 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 817) = 3 ^ 7 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_817.1, data_15_817.2]

/-- Complete interval computation for depth 15, residue 818. -/
theorem bounds_15_818 : exactInterval 15 818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_818 : oddCount 818 15 = 7 ∧ acceleratedOrbit 15 818 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 818) = 3 ^ 7 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_818.1, data_15_818.2]

end Collatz.Research.PassageAtlas.Batch0025
