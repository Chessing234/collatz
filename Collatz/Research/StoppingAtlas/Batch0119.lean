import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0119

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 788. -/
theorem bounds_11_788 : exactInterval 11 788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_788 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 788) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_788 : oddCount 788 11 = 3 ∧ acceleratedOrbit 11 788 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_788 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 788) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_788.1, data_11_788.2]

/-- Complete interval computation for depth 11, residue 789. -/
theorem bounds_11_789 : exactInterval 11 789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_789 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 789) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_789 : oddCount 789 11 = 3 ∧ acceleratedOrbit 11 789 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_789 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 789) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_789.1, data_11_789.2]

/-- Complete interval computation for depth 11, residue 790. -/
theorem bounds_11_790 : exactInterval 11 790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_790 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 790) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_790 : oddCount 790 11 = 6 ∧ acceleratedOrbit 11 790 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_790 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 790) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_790.1, data_11_790.2]

/-- Complete interval computation for depth 11, residue 791. -/
theorem bounds_11_791 : exactInterval 11 791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_791 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 791) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_791 : oddCount 791 11 = 6 ∧ acceleratedOrbit 11 791 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_791 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 791) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_791.1, data_11_791.2]

/-- Complete interval computation for depth 11, residue 792. -/
theorem bounds_11_792 : exactInterval 11 792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_792 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 792) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_792 : oddCount 792 11 = 3 ∧ acceleratedOrbit 11 792 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_792 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 792) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_792.1, data_11_792.2]

/-- Complete interval computation for depth 11, residue 793. -/
theorem bounds_11_793 : exactInterval 11 793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_793 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 793) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_793 : oddCount 793 11 = 7 ∧ acceleratedOrbit 11 793 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_793 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 793) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_793.1, data_11_793.2]

/-- Complete interval computation for depth 11, residue 794. -/
theorem bounds_11_794 : exactInterval 11 794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_794 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 794) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_794 : oddCount 794 11 = 3 ∧ acceleratedOrbit 11 794 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_794 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 794) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_794.1, data_11_794.2]

/-- Complete interval computation for depth 11, residue 795. -/
theorem bounds_11_795 : exactInterval 11 795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_795 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 795) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_795 : oddCount 795 11 = 9 ∧ acceleratedOrbit 11 795 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_795 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 795) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_795.1, data_11_795.2]

/-- Complete interval computation for depth 11, residue 796. -/
theorem bounds_11_796 : exactInterval 11 796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_796 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 796) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_796 : oddCount 796 11 = 5 ∧ acceleratedOrbit 11 796 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_796 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 796) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_796.1, data_11_796.2]

/-- Complete interval computation for depth 11, residue 797. -/
theorem bounds_11_797 : exactInterval 11 797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_797 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 797) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_797 : oddCount 797 11 = 5 ∧ acceleratedOrbit 11 797 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_797 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 797) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_797.1, data_11_797.2]

/-- Complete interval computation for depth 11, residue 798. -/
theorem bounds_11_798 : exactInterval 11 798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_798 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 798) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_798 : oddCount 798 11 = 5 ∧ acceleratedOrbit 11 798 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_798 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 798) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_798.1, data_11_798.2]

/-- Complete interval computation for depth 11, residue 799. -/
theorem bounds_11_799 : exactInterval 11 799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_799 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 799) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_799 : oddCount 799 11 = 8 ∧ acceleratedOrbit 11 799 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_799 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 799) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_799.1, data_11_799.2]

/-- Complete interval computation for depth 11, residue 800. -/
theorem bounds_11_800 : exactInterval 11 800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_800 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 800) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_800 : oddCount 800 11 = 3 ∧ acceleratedOrbit 11 800 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_800 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 800) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_800.1, data_11_800.2]

/-- Complete interval computation for depth 11, residue 801. -/
theorem bounds_11_801 : exactInterval 11 801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_801 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 801) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_801 : oddCount 801 11 = 6 ∧ acceleratedOrbit 11 801 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_801 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 801) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_801.1, data_11_801.2]

/-- Complete interval computation for depth 11, residue 802. -/
theorem bounds_11_802 : exactInterval 11 802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_802 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 802) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_802 : oddCount 802 11 = 4 ∧ acceleratedOrbit 11 802 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_802 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 802) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_802.1, data_11_802.2]

end Collatz.Research.StoppingAtlas.Batch0119
