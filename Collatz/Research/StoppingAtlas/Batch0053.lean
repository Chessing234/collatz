import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0053

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 798. -/
theorem bounds_10_798 : exactInterval 10 798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_798 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 798) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_798 : oddCount 798 10 = 5 ∧ acceleratedOrbit 10 798 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_798 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 798) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_798.1, data_10_798.2]

/-- Complete interval computation for depth 10, residue 799. -/
theorem bounds_10_799 : exactInterval 10 799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_799 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 799) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_799 : oddCount 799 10 = 7 ∧ acceleratedOrbit 10 799 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_799 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 799) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_799.1, data_10_799.2]

/-- Complete interval computation for depth 10, residue 800. -/
theorem bounds_10_800 : exactInterval 10 800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_800 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 800) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_800 : oddCount 800 10 = 3 ∧ acceleratedOrbit 10 800 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_800 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 800) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_800.1, data_10_800.2]

/-- Complete interval computation for depth 10, residue 801. -/
theorem bounds_10_801 : exactInterval 10 801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_801 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 801) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_801 : oddCount 801 10 = 5 ∧ acceleratedOrbit 10 801 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_801 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 801) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_801.1, data_10_801.2]

/-- Complete interval computation for depth 10, residue 802. -/
theorem bounds_10_802 : exactInterval 10 802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_802 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 802) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_802 : oddCount 802 10 = 4 ∧ acceleratedOrbit 10 802 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_802 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 802) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_802.1, data_10_802.2]

/-- Complete interval computation for depth 10, residue 803. -/
theorem bounds_10_803 : exactInterval 10 803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_803 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 803) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_803 : oddCount 803 10 = 4 ∧ acceleratedOrbit 10 803 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_803 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 803) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_803.1, data_10_803.2]

/-- Complete interval computation for depth 10, residue 804. -/
theorem bounds_10_804 : exactInterval 10 804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_804 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 804) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_804 : oddCount 804 10 = 4 ∧ acceleratedOrbit 10 804 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_804 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 804) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_804.1, data_10_804.2]

/-- Complete interval computation for depth 10, residue 805. -/
theorem bounds_10_805 : exactInterval 10 805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_805 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 805) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_805 : oddCount 805 10 = 4 ∧ acceleratedOrbit 10 805 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_805 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 805) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_805.1, data_10_805.2]

/-- Complete interval computation for depth 10, residue 806. -/
theorem bounds_10_806 : exactInterval 10 806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_806 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 806) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_806 : oddCount 806 10 = 4 ∧ acceleratedOrbit 10 806 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_806 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 806) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_806.1, data_10_806.2]

/-- Complete interval computation for depth 10, residue 807. -/
theorem bounds_10_807 : exactInterval 10 807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_807 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 807) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_807 : oddCount 807 10 = 7 ∧ acceleratedOrbit 10 807 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_807 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 807) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_807.1, data_10_807.2]

/-- Complete interval computation for depth 10, residue 808. -/
theorem bounds_10_808 : exactInterval 10 808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_808 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 808) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_808 : oddCount 808 10 = 3 ∧ acceleratedOrbit 10 808 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_808 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 808) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_808.1, data_10_808.2]

/-- Complete interval computation for depth 10, residue 809. -/
theorem bounds_10_809 : exactInterval 10 809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_809 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 809) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_809 : oddCount 809 10 = 6 ∧ acceleratedOrbit 10 809 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_809 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 809) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_809.1, data_10_809.2]

/-- Complete interval computation for depth 10, residue 810. -/
theorem bounds_10_810 : exactInterval 10 810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_810 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 810) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_810 : oddCount 810 10 = 3 ∧ acceleratedOrbit 10 810 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_810 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 810) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_810.1, data_10_810.2]

/-- Complete interval computation for depth 10, residue 811. -/
theorem bounds_10_811 : exactInterval 10 811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_811 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 811) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_811 : oddCount 811 10 = 5 ∧ acceleratedOrbit 10 811 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_811 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 811) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_811.1, data_10_811.2]

/-- Complete interval computation for depth 10, residue 812. -/
theorem bounds_10_812 : exactInterval 10 812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_812 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 812) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_812 : oddCount 812 10 = 4 ∧ acceleratedOrbit 10 812 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_812 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 812) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_812.1, data_10_812.2]

/-- Complete interval computation for depth 10, residue 813. -/
theorem bounds_10_813 : exactInterval 10 813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_813 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 813) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_813 : oddCount 813 10 = 4 ∧ acceleratedOrbit 10 813 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_813 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 813) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_813.1, data_10_813.2]

end Collatz.Research.StoppingAtlas.Batch0053
