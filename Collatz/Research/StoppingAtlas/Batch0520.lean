import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0520

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 803. -/
theorem bounds_13_803 : exactInterval 13 803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_803 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 803) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_803 : oddCount 803 13 = 4 ∧ acceleratedOrbit 13 803 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_803 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 803) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_803.1, data_13_803.2]

/-- Complete interval computation for depth 13, residue 804. -/
theorem bounds_13_804 : exactInterval 13 804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_804 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 804) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_804 : oddCount 804 13 = 4 ∧ acceleratedOrbit 13 804 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_804 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 804) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_804.1, data_13_804.2]

/-- Complete interval computation for depth 13, residue 805. -/
theorem bounds_13_805 : exactInterval 13 805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_805 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 805) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_805 : oddCount 805 13 = 4 ∧ acceleratedOrbit 13 805 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_805 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 805) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_805.1, data_13_805.2]

/-- Complete interval computation for depth 13, residue 806. -/
theorem bounds_13_806 : exactInterval 13 806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_806 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 806) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_806 : oddCount 806 13 = 4 ∧ acceleratedOrbit 13 806 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_806 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 806) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_806.1, data_13_806.2]

/-- Complete interval computation for depth 13, residue 807. -/
theorem bounds_13_807 : exactInterval 13 807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_807 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 807) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_807 : oddCount 807 13 = 10 ∧ acceleratedOrbit 13 807 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_807 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 807) = 3 ^ 10 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_807.1, data_13_807.2]

/-- Complete interval computation for depth 13, residue 808. -/
theorem bounds_13_808 : exactInterval 13 808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_808 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 808) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_808 : oddCount 808 13 = 5 ∧ acceleratedOrbit 13 808 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_808 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 808) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_808.1, data_13_808.2]

/-- Complete interval computation for depth 13, residue 809. -/
theorem bounds_13_809 : exactInterval 13 809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_809 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 809) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_809 : oddCount 809 13 = 8 ∧ acceleratedOrbit 13 809 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_809 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 809) = 3 ^ 8 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_809.1, data_13_809.2]

/-- Complete interval computation for depth 13, residue 810. -/
theorem bounds_13_810 : exactInterval 13 810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_810 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 810) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_810 : oddCount 810 13 = 5 ∧ acceleratedOrbit 13 810 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_810 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 810) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_810.1, data_13_810.2]

/-- Complete interval computation for depth 13, residue 811. -/
theorem bounds_13_811 : exactInterval 13 811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_811 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 811) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_811 : oddCount 811 13 = 7 ∧ acceleratedOrbit 13 811 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_811 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 811) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_811.1, data_13_811.2]

/-- Complete interval computation for depth 13, residue 812. -/
theorem bounds_13_812 : exactInterval 13 812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_812 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 812) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_812 : oddCount 812 13 = 6 ∧ acceleratedOrbit 13 812 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_812 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 812) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_812.1, data_13_812.2]

/-- Complete interval computation for depth 13, residue 813. -/
theorem bounds_13_813 : exactInterval 13 813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_813 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 813) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_813 : oddCount 813 13 = 6 ∧ acceleratedOrbit 13 813 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_813 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 813) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_813.1, data_13_813.2]

/-- Complete interval computation for depth 13, residue 814. -/
theorem bounds_13_814 : exactInterval 13 814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_814 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 814) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_814 : oddCount 814 13 = 6 ∧ acceleratedOrbit 13 814 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_814 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 814) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_814.1, data_13_814.2]

/-- Complete interval computation for depth 13, residue 815. -/
theorem bounds_13_815 : exactInterval 13 815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_815 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 815) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_815 : oddCount 815 13 = 7 ∧ acceleratedOrbit 13 815 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_815 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 815) = 3 ^ 7 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_815.1, data_13_815.2]

/-- Complete interval computation for depth 13, residue 816. -/
theorem bounds_13_816 : exactInterval 13 816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_816 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 816) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_816 : oddCount 816 13 = 5 ∧ acceleratedOrbit 13 816 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_816 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 816) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_816.1, data_13_816.2]

/-- Complete interval computation for depth 13, residue 817. -/
theorem bounds_13_817 : exactInterval 13 817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_817 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 817) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_817 : oddCount 817 13 = 6 ∧ acceleratedOrbit 13 817 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_817 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 817) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_817.1, data_13_817.2]

/-- Complete interval computation for depth 13, residue 818. -/
theorem bounds_13_818 : exactInterval 13 818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_818 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 818) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_818 : oddCount 818 13 = 6 ∧ acceleratedOrbit 13 818 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_818 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 818) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_818.1, data_13_818.2]

end Collatz.Research.StoppingAtlas.Batch0520
