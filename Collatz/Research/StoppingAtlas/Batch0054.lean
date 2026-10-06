import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0054

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 814. -/
theorem bounds_10_814 : exactInterval 10 814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_814 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 814) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_814 : oddCount 814 10 = 4 ∧ acceleratedOrbit 10 814 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_814 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 814) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_814.1, data_10_814.2]

/-- Complete interval computation for depth 10, residue 815. -/
theorem bounds_10_815 : exactInterval 10 815 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_815 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 815) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_815 : oddCount 815 10 = 6 ∧ acceleratedOrbit 10 815 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_815 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 815) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_815.1, data_10_815.2]

/-- Complete interval computation for depth 10, residue 816. -/
theorem bounds_10_816 : exactInterval 10 816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_816 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 816) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_816 : oddCount 816 10 = 3 ∧ acceleratedOrbit 10 816 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_816 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 816) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_816.1, data_10_816.2]

/-- Complete interval computation for depth 10, residue 817. -/
theorem bounds_10_817 : exactInterval 10 817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_817 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 817) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_817 : oddCount 817 10 = 4 ∧ acceleratedOrbit 10 817 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_817 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 817) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_817.1, data_10_817.2]

/-- Complete interval computation for depth 10, residue 818. -/
theorem bounds_10_818 : exactInterval 10 818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_818 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 818) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_818 : oddCount 818 10 = 4 ∧ acceleratedOrbit 10 818 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_818 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 818) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_818.1, data_10_818.2]

/-- Complete interval computation for depth 10, residue 819. -/
theorem bounds_10_819 : exactInterval 10 819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_819 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 819) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_819 : oddCount 819 10 = 4 ∧ acceleratedOrbit 10 819 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_819 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 819) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_819.1, data_10_819.2]

/-- Complete interval computation for depth 10, residue 820. -/
theorem bounds_10_820 : exactInterval 10 820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_820 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 820) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_820 : oddCount 820 10 = 3 ∧ acceleratedOrbit 10 820 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_820 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 820) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_820.1, data_10_820.2]

/-- Complete interval computation for depth 10, residue 821. -/
theorem bounds_10_821 : exactInterval 10 821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_821 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 821) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_821 : oddCount 821 10 = 3 ∧ acceleratedOrbit 10 821 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_821 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 821) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_821.1, data_10_821.2]

/-- Complete interval computation for depth 10, residue 822. -/
theorem bounds_10_822 : exactInterval 10 822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_822 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 822) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_822 : oddCount 822 10 = 6 ∧ acceleratedOrbit 10 822 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_822 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 822) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_822.1, data_10_822.2]

/-- Complete interval computation for depth 10, residue 823. -/
theorem bounds_10_823 : exactInterval 10 823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_823 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 823) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_823 : oddCount 823 10 = 6 ∧ acceleratedOrbit 10 823 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_823 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 823) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_823.1, data_10_823.2]

/-- Complete interval computation for depth 10, residue 824. -/
theorem bounds_10_824 : exactInterval 10 824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_824 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 824) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_824 : oddCount 824 10 = 6 ∧ acceleratedOrbit 10 824 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_824 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 824) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_824.1, data_10_824.2]

/-- Complete interval computation for depth 10, residue 825. -/
theorem bounds_10_825 : exactInterval 10 825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_825 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 825) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_825 : oddCount 825 10 = 6 ∧ acceleratedOrbit 10 825 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_825 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 825) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_825.1, data_10_825.2]

/-- Complete interval computation for depth 10, residue 826. -/
theorem bounds_10_826 : exactInterval 10 826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_826 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 826) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_826 : oddCount 826 10 = 6 ∧ acceleratedOrbit 10 826 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_826 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 826) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_826.1, data_10_826.2]

/-- Complete interval computation for depth 10, residue 827. -/
theorem bounds_10_827 : exactInterval 10 827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_827 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 827) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_827 : oddCount 827 10 = 5 ∧ acceleratedOrbit 10 827 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_827 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 827) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_827.1, data_10_827.2]

/-- Complete interval computation for depth 10, residue 828. -/
theorem bounds_10_828 : exactInterval 10 828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_828 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 828) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_828 : oddCount 828 10 = 6 ∧ acceleratedOrbit 10 828 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_828 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 828) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_828.1, data_10_828.2]

end Collatz.Research.StoppingAtlas.Batch0054
