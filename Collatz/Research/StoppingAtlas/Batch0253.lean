import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0253

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 798. -/
theorem bounds_12_798 : exactInterval 12 798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_798 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 798) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_798 : oddCount 798 12 = 6 ∧ acceleratedOrbit 12 798 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_798 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 798) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_798.1, data_12_798.2]

/-- Complete interval computation for depth 12, residue 799. -/
theorem bounds_12_799 : exactInterval 12 799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_799 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 799) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_799 : oddCount 799 12 = 8 ∧ acceleratedOrbit 12 799 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_799 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 799) = 3 ^ 8 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_799.1, data_12_799.2]

/-- Complete interval computation for depth 12, residue 800. -/
theorem bounds_12_800 : exactInterval 12 800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_800 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 800) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_800 : oddCount 800 12 = 4 ∧ acceleratedOrbit 12 800 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_800 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 800) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_800.1, data_12_800.2]

/-- Complete interval computation for depth 12, residue 801. -/
theorem bounds_12_801 : exactInterval 12 801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_801 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 801) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_801 : oddCount 801 12 = 7 ∧ acceleratedOrbit 12 801 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_801 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 801) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_801.1, data_12_801.2]

/-- Complete interval computation for depth 12, residue 802. -/
theorem bounds_12_802 : exactInterval 12 802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_802 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 802) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_802 : oddCount 802 12 = 4 ∧ acceleratedOrbit 12 802 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_802 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 802) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_802.1, data_12_802.2]

/-- Complete interval computation for depth 12, residue 803. -/
theorem bounds_12_803 : exactInterval 12 803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_803 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 803) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_803 : oddCount 803 12 = 4 ∧ acceleratedOrbit 12 803 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_803 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 803) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_803.1, data_12_803.2]

/-- Complete interval computation for depth 12, residue 804. -/
theorem bounds_12_804 : exactInterval 12 804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_804 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 804) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_804 : oddCount 804 12 = 4 ∧ acceleratedOrbit 12 804 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_804 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 804) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_804.1, data_12_804.2]

/-- Complete interval computation for depth 12, residue 805. -/
theorem bounds_12_805 : exactInterval 12 805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_805 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 805) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_805 : oddCount 805 12 = 4 ∧ acceleratedOrbit 12 805 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_805 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 805) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_805.1, data_12_805.2]

/-- Complete interval computation for depth 12, residue 806. -/
theorem bounds_12_806 : exactInterval 12 806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_806 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 806) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_806 : oddCount 806 12 = 4 ∧ acceleratedOrbit 12 806 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_806 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 806) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_806.1, data_12_806.2]

/-- Complete interval computation for depth 12, residue 807. -/
theorem bounds_12_807 : exactInterval 12 807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_807 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 807) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_807 : oddCount 807 12 = 9 ∧ acceleratedOrbit 12 807 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_807 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 807) = 3 ^ 9 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_807.1, data_12_807.2]

/-- Complete interval computation for depth 12, residue 808. -/
theorem bounds_12_808 : exactInterval 12 808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_808 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 808) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_808 : oddCount 808 12 = 4 ∧ acceleratedOrbit 12 808 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_808 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 808) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_808.1, data_12_808.2]

/-- Complete interval computation for depth 12, residue 809. -/
theorem bounds_12_809 : exactInterval 12 809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_809 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 809) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_809 : oddCount 809 12 = 7 ∧ acceleratedOrbit 12 809 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_809 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 809) = 3 ^ 7 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_809.1, data_12_809.2]

/-- Complete interval computation for depth 12, residue 810. -/
theorem bounds_12_810 : exactInterval 12 810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_810 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 810) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_810 : oddCount 810 12 = 4 ∧ acceleratedOrbit 12 810 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_810 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 810) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_810.1, data_12_810.2]

/-- Complete interval computation for depth 12, residue 811. -/
theorem bounds_12_811 : exactInterval 12 811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_811 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 811) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_811 : oddCount 811 12 = 6 ∧ acceleratedOrbit 12 811 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_811 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 811) = 3 ^ 6 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_811.1, data_12_811.2]

/-- Complete interval computation for depth 12, residue 812. -/
theorem bounds_12_812 : exactInterval 12 812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_812 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 812) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_812 : oddCount 812 12 = 5 ∧ acceleratedOrbit 12 812 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_812 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 812) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_812.1, data_12_812.2]

/-- Complete interval computation for depth 12, residue 813. -/
theorem bounds_12_813 : exactInterval 12 813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_813 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 813) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_813 : oddCount 813 12 = 5 ∧ acceleratedOrbit 12 813 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_813 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 813) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_813.1, data_12_813.2]

end Collatz.Research.StoppingAtlas.Batch0253
