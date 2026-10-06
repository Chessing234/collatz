import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0519

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 788. -/
theorem bounds_13_788 : exactInterval 13 788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_788 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 788) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_788 : oddCount 788 13 = 5 ∧ acceleratedOrbit 13 788 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_788 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 788) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_788.1, data_13_788.2]

/-- Complete interval computation for depth 13, residue 789. -/
theorem bounds_13_789 : exactInterval 13 789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_789 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 789) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_789 : oddCount 789 13 = 5 ∧ acceleratedOrbit 13 789 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_789 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 789) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_789.1, data_13_789.2]

/-- Complete interval computation for depth 13, residue 790. -/
theorem bounds_13_790 : exactInterval 13 790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_790 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 790) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_790 : oddCount 790 13 = 8 ∧ acceleratedOrbit 13 790 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_790 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 790) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_790.1, data_13_790.2]

/-- Complete interval computation for depth 13, residue 791. -/
theorem bounds_13_791 : exactInterval 13 791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_791 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 791) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_791 : oddCount 791 13 = 8 ∧ acceleratedOrbit 13 791 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_791 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 791) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_791.1, data_13_791.2]

/-- Complete interval computation for depth 13, residue 792. -/
theorem bounds_13_792 : exactInterval 13 792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_792 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 792) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_792 : oddCount 792 13 = 5 ∧ acceleratedOrbit 13 792 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_792 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 792) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_792.1, data_13_792.2]

/-- Complete interval computation for depth 13, residue 793. -/
theorem bounds_13_793 : exactInterval 13 793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_793 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 793) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_793 : oddCount 793 13 = 8 ∧ acceleratedOrbit 13 793 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_793 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 793) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_793.1, data_13_793.2]

/-- Complete interval computation for depth 13, residue 794. -/
theorem bounds_13_794 : exactInterval 13 794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_794 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 794) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_794 : oddCount 794 13 = 5 ∧ acceleratedOrbit 13 794 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_794 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 794) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_794.1, data_13_794.2]

/-- Complete interval computation for depth 13, residue 795. -/
theorem bounds_13_795 : exactInterval 13 795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_795 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 795) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_795 : oddCount 795 13 = 10 ∧ acceleratedOrbit 13 795 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_795 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 795) = 3 ^ 10 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_795.1, data_13_795.2]

/-- Complete interval computation for depth 13, residue 796. -/
theorem bounds_13_796 : exactInterval 13 796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_796 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 796) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_796 : oddCount 796 13 = 7 ∧ acceleratedOrbit 13 796 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_796 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 796) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_796.1, data_13_796.2]

/-- Complete interval computation for depth 13, residue 797. -/
theorem bounds_13_797 : exactInterval 13 797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_797 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 797) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_797 : oddCount 797 13 = 7 ∧ acceleratedOrbit 13 797 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_797 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 797) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_797.1, data_13_797.2]

/-- Complete interval computation for depth 13, residue 798. -/
theorem bounds_13_798 : exactInterval 13 798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_798 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 798) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_798 : oddCount 798 13 = 7 ∧ acceleratedOrbit 13 798 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_798 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 798) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_798.1, data_13_798.2]

/-- Complete interval computation for depth 13, residue 799. -/
theorem bounds_13_799 : exactInterval 13 799 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_799 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 799) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_799 : oddCount 799 13 = 8 ∧ acceleratedOrbit 13 799 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_799 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 799) = 3 ^ 8 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_799.1, data_13_799.2]

/-- Complete interval computation for depth 13, residue 800. -/
theorem bounds_13_800 : exactInterval 13 800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_800 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 800) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_800 : oddCount 800 13 = 5 ∧ acceleratedOrbit 13 800 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_800 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 800) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_800.1, data_13_800.2]

/-- Complete interval computation for depth 13, residue 801. -/
theorem bounds_13_801 : exactInterval 13 801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_801 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 801) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_801 : oddCount 801 13 = 8 ∧ acceleratedOrbit 13 801 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_801 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 801) = 3 ^ 8 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_801.1, data_13_801.2]

/-- Complete interval computation for depth 13, residue 802. -/
theorem bounds_13_802 : exactInterval 13 802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_802 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 802) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_802 : oddCount 802 13 = 4 ∧ acceleratedOrbit 13 802 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_802 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 802) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_802.1, data_13_802.2]

end Collatz.Research.StoppingAtlas.Batch0519
