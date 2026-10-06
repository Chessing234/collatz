import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0781

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4812. -/
theorem bounds_13_4812 : exactInterval 13 4812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4812 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4812) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4812 : oddCount 4812 13 = 6 ∧ acceleratedOrbit 13 4812 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4812 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4812) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4812.1, data_13_4812.2]

/-- Complete interval computation for depth 13, residue 4813. -/
theorem bounds_13_4813 : exactInterval 13 4813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4813 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4813) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4813 : oddCount 4813 13 = 6 ∧ acceleratedOrbit 13 4813 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4813 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4813) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4813.1, data_13_4813.2]

/-- Complete interval computation for depth 13, residue 4814. -/
theorem bounds_13_4814 : exactInterval 13 4814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4814 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4814) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4814 : oddCount 4814 13 = 9 ∧ acceleratedOrbit 13 4814 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4814 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4814) = 3 ^ 9 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4814.1, data_13_4814.2]

/-- Complete interval computation for depth 13, residue 4815. -/
theorem bounds_13_4815 : exactInterval 13 4815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4815 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4815) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4815 : oddCount 4815 13 = 9 ∧ acceleratedOrbit 13 4815 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4815 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4815) = 3 ^ 9 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4815.1, data_13_4815.2]

/-- Complete interval computation for depth 13, residue 4816. -/
theorem bounds_13_4816 : exactInterval 13 4816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4816 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4816) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4816 : oddCount 4816 13 = 3 ∧ acceleratedOrbit 13 4816 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4816 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4816) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4816.1, data_13_4816.2]

/-- Complete interval computation for depth 13, residue 4817. -/
theorem bounds_13_4817 : exactInterval 13 4817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4817 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4817) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4817 : oddCount 4817 13 = 5 ∧ acceleratedOrbit 13 4817 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4817 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4817) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4817.1, data_13_4817.2]

/-- Complete interval computation for depth 13, residue 4818. -/
theorem bounds_13_4818 : exactInterval 13 4818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4818 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4818) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4818 : oddCount 4818 13 = 5 ∧ acceleratedOrbit 13 4818 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4818 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4818) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4818.1, data_13_4818.2]

/-- Complete interval computation for depth 13, residue 4819. -/
theorem bounds_13_4819 : exactInterval 13 4819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4819 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4819) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4819 : oddCount 4819 13 = 5 ∧ acceleratedOrbit 13 4819 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4819 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4819) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4819.1, data_13_4819.2]

/-- Complete interval computation for depth 13, residue 4820. -/
theorem bounds_13_4820 : exactInterval 13 4820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4820 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4820) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4820 : oddCount 4820 13 = 3 ∧ acceleratedOrbit 13 4820 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4820 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4820) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4820.1, data_13_4820.2]

/-- Complete interval computation for depth 13, residue 4821. -/
theorem bounds_13_4821 : exactInterval 13 4821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4821 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4821) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4821 : oddCount 4821 13 = 3 ∧ acceleratedOrbit 13 4821 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4821 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4821) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4821.1, data_13_4821.2]

/-- Complete interval computation for depth 13, residue 4822. -/
theorem bounds_13_4822 : exactInterval 13 4822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4822 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4822) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4822 : oddCount 4822 13 = 7 ∧ acceleratedOrbit 13 4822 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4822 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4822) = 3 ^ 7 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4822.1, data_13_4822.2]

/-- Complete interval computation for depth 13, residue 4823. -/
theorem bounds_13_4823 : exactInterval 13 4823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4823 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4823) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4823 : oddCount 4823 13 = 7 ∧ acceleratedOrbit 13 4823 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4823 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4823) = 3 ^ 7 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4823.1, data_13_4823.2]

/-- Complete interval computation for depth 13, residue 4824. -/
theorem bounds_13_4824 : exactInterval 13 4824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4824 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4824) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4824 : oddCount 4824 13 = 7 ∧ acceleratedOrbit 13 4824 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4824 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4824) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4824.1, data_13_4824.2]

/-- Complete interval computation for depth 13, residue 4825. -/
theorem bounds_13_4825 : exactInterval 13 4825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4825 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4825) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4825 : oddCount 4825 13 = 6 ∧ acceleratedOrbit 13 4825 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4825 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4825) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4825.1, data_13_4825.2]

/-- Complete interval computation for depth 13, residue 4826. -/
theorem bounds_13_4826 : exactInterval 13 4826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4826 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4826) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4826 : oddCount 4826 13 = 7 ∧ acceleratedOrbit 13 4826 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4826 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4826) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4826.1, data_13_4826.2]

/-- Complete interval computation for depth 13, residue 4827. -/
theorem bounds_13_4827 : exactInterval 13 4827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4827 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4827) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4827 : oddCount 4827 13 = 9 ∧ acceleratedOrbit 13 4827 = 11603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4827 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4827) = 3 ^ 9 * m + 11603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4827.1, data_13_4827.2]

end Collatz.Research.StoppingAtlas.Batch0781
