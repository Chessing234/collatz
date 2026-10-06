import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0254

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 814. -/
theorem bounds_12_814 : exactInterval 12 814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_814 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 814) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_814 : oddCount 814 12 = 5 ∧ acceleratedOrbit 12 814 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_814 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 814) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_814.1, data_12_814.2]

/-- Complete interval computation for depth 12, residue 815. -/
theorem bounds_12_815 : exactInterval 12 815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_815 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 815) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_815 : oddCount 815 12 = 7 ∧ acceleratedOrbit 12 815 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_815 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 815) = 3 ^ 7 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_815.1, data_12_815.2]

/-- Complete interval computation for depth 12, residue 816. -/
theorem bounds_12_816 : exactInterval 12 816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_816 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 816) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_816 : oddCount 816 12 = 4 ∧ acceleratedOrbit 12 816 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_816 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 816) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_816.1, data_12_816.2]

/-- Complete interval computation for depth 12, residue 817. -/
theorem bounds_12_817 : exactInterval 12 817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_817 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 817) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_817 : oddCount 817 12 = 5 ∧ acceleratedOrbit 12 817 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_817 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 817) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_817.1, data_12_817.2]

/-- Complete interval computation for depth 12, residue 818. -/
theorem bounds_12_818 : exactInterval 12 818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_818 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 818) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_818 : oddCount 818 12 = 5 ∧ acceleratedOrbit 12 818 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_818 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 818) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_818.1, data_12_818.2]

/-- Complete interval computation for depth 12, residue 819. -/
theorem bounds_12_819 : exactInterval 12 819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_819 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 819) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_819 : oddCount 819 12 = 5 ∧ acceleratedOrbit 12 819 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_819 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 819) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_819.1, data_12_819.2]

/-- Complete interval computation for depth 12, residue 820. -/
theorem bounds_12_820 : exactInterval 12 820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_820 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 820) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_820 : oddCount 820 12 = 4 ∧ acceleratedOrbit 12 820 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_820 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 820) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_820.1, data_12_820.2]

/-- Complete interval computation for depth 12, residue 821. -/
theorem bounds_12_821 : exactInterval 12 821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_821 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 821) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_821 : oddCount 821 12 = 4 ∧ acceleratedOrbit 12 821 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_821 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 821) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_821.1, data_12_821.2]

/-- Complete interval computation for depth 12, residue 822. -/
theorem bounds_12_822 : exactInterval 12 822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_822 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 822) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_822 : oddCount 822 12 = 8 ∧ acceleratedOrbit 12 822 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_822 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 822) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_822.1, data_12_822.2]

/-- Complete interval computation for depth 12, residue 823. -/
theorem bounds_12_823 : exactInterval 12 823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_823 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 823) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_823 : oddCount 823 12 = 8 ∧ acceleratedOrbit 12 823 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_823 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 823) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_823.1, data_12_823.2]

/-- Complete interval computation for depth 12, residue 824. -/
theorem bounds_12_824 : exactInterval 12 824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_824 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 824) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_824 : oddCount 824 12 = 7 ∧ acceleratedOrbit 12 824 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_824 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 824) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_824.1, data_12_824.2]

/-- Complete interval computation for depth 12, residue 825. -/
theorem bounds_12_825 : exactInterval 12 825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_825 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 825) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_825 : oddCount 825 12 = 7 ∧ acceleratedOrbit 12 825 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_825 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 825) = 3 ^ 7 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_825.1, data_12_825.2]

/-- Complete interval computation for depth 12, residue 826. -/
theorem bounds_12_826 : exactInterval 12 826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_826 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 826) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_826 : oddCount 826 12 = 7 ∧ acceleratedOrbit 12 826 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_826 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 826) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_826.1, data_12_826.2]

/-- Complete interval computation for depth 12, residue 827. -/
theorem bounds_12_827 : exactInterval 12 827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_827 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 827) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_827 : oddCount 827 12 = 6 ∧ acceleratedOrbit 12 827 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_827 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 827) = 3 ^ 6 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_827.1, data_12_827.2]

/-- Complete interval computation for depth 12, residue 828. -/
theorem bounds_12_828 : exactInterval 12 828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_828 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 828) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_828 : oddCount 828 12 = 7 ∧ acceleratedOrbit 12 828 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_828 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 828) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_828.1, data_12_828.2]

end Collatz.Research.StoppingAtlas.Batch0254
