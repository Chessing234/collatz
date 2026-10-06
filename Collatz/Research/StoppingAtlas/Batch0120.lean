import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0120

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 803. -/
theorem bounds_11_803 : exactInterval 11 803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_803 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 803) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_803 : oddCount 803 11 = 4 ∧ acceleratedOrbit 11 803 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_803 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 803) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_803.1, data_11_803.2]

/-- Complete interval computation for depth 11, residue 804. -/
theorem bounds_11_804 : exactInterval 11 804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_804 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 804) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_804 : oddCount 804 11 = 4 ∧ acceleratedOrbit 11 804 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_804 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 804) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_804.1, data_11_804.2]

/-- Complete interval computation for depth 11, residue 805. -/
theorem bounds_11_805 : exactInterval 11 805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_805 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 805) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_805 : oddCount 805 11 = 4 ∧ acceleratedOrbit 11 805 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_805 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 805) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_805.1, data_11_805.2]

/-- Complete interval computation for depth 11, residue 806. -/
theorem bounds_11_806 : exactInterval 11 806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_806 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 806) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_806 : oddCount 806 11 = 4 ∧ acceleratedOrbit 11 806 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_806 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 806) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_806.1, data_11_806.2]

/-- Complete interval computation for depth 11, residue 807. -/
theorem bounds_11_807 : exactInterval 11 807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_807 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 807) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_807 : oddCount 807 11 = 8 ∧ acceleratedOrbit 11 807 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_807 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 807) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_807.1, data_11_807.2]

/-- Complete interval computation for depth 11, residue 808. -/
theorem bounds_11_808 : exactInterval 11 808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_808 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 808) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_808 : oddCount 808 11 = 3 ∧ acceleratedOrbit 11 808 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_808 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 808) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_808.1, data_11_808.2]

/-- Complete interval computation for depth 11, residue 809. -/
theorem bounds_11_809 : exactInterval 11 809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_809 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 809) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_809 : oddCount 809 11 = 7 ∧ acceleratedOrbit 11 809 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_809 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 809) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_809.1, data_11_809.2]

/-- Complete interval computation for depth 11, residue 810. -/
theorem bounds_11_810 : exactInterval 11 810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_810 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 810) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_810 : oddCount 810 11 = 3 ∧ acceleratedOrbit 11 810 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_810 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 810) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_810.1, data_11_810.2]

/-- Complete interval computation for depth 11, residue 811. -/
theorem bounds_11_811 : exactInterval 11 811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_811 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 811) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_811 : oddCount 811 11 = 6 ∧ acceleratedOrbit 11 811 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_811 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 811) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_811.1, data_11_811.2]

/-- Complete interval computation for depth 11, residue 812. -/
theorem bounds_11_812 : exactInterval 11 812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_812 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 812) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_812 : oddCount 812 11 = 5 ∧ acceleratedOrbit 11 812 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_812 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 812) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_812.1, data_11_812.2]

/-- Complete interval computation for depth 11, residue 813. -/
theorem bounds_11_813 : exactInterval 11 813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_813 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 813) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_813 : oddCount 813 11 = 5 ∧ acceleratedOrbit 11 813 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_813 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 813) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_813.1, data_11_813.2]

/-- Complete interval computation for depth 11, residue 814. -/
theorem bounds_11_814 : exactInterval 11 814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_814 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 814) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_814 : oddCount 814 11 = 5 ∧ acceleratedOrbit 11 814 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_814 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 814) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_814.1, data_11_814.2]

/-- Complete interval computation for depth 11, residue 815. -/
theorem bounds_11_815 : exactInterval 11 815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_815 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 815) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_815 : oddCount 815 11 = 7 ∧ acceleratedOrbit 11 815 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_815 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 815) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_815.1, data_11_815.2]

/-- Complete interval computation for depth 11, residue 816. -/
theorem bounds_11_816 : exactInterval 11 816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_816 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 816) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_816 : oddCount 816 11 = 3 ∧ acceleratedOrbit 11 816 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_816 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 816) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_816.1, data_11_816.2]

/-- Complete interval computation for depth 11, residue 817. -/
theorem bounds_11_817 : exactInterval 11 817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_817 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 817) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_817 : oddCount 817 11 = 5 ∧ acceleratedOrbit 11 817 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_817 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 817) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_817.1, data_11_817.2]

/-- Complete interval computation for depth 11, residue 818. -/
theorem bounds_11_818 : exactInterval 11 818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_818 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 818) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_818 : oddCount 818 11 = 5 ∧ acceleratedOrbit 11 818 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_818 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 818) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_818.1, data_11_818.2]

end Collatz.Research.StoppingAtlas.Batch0120
