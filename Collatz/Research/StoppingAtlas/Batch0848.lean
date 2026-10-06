import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0848

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5841. -/
theorem bounds_13_5841 : exactInterval 13 5841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5841 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5841) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5841 : oddCount 5841 13 = 7 ∧ acceleratedOrbit 13 5841 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5841 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5841) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5841.1, data_13_5841.2]

/-- Complete interval computation for depth 13, residue 5842. -/
theorem bounds_13_5842 : exactInterval 13 5842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5842 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5842) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5842 : oddCount 5842 13 = 7 ∧ acceleratedOrbit 13 5842 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5842 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5842) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5842.1, data_13_5842.2]

/-- Complete interval computation for depth 13, residue 5843. -/
theorem bounds_13_5843 : exactInterval 13 5843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5843 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5843) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5843 : oddCount 5843 13 = 7 ∧ acceleratedOrbit 13 5843 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5843 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5843) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5843.1, data_13_5843.2]

/-- Complete interval computation for depth 13, residue 5844. -/
theorem bounds_13_5844 : exactInterval 13 5844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5844 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5844) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5844 : oddCount 5844 13 = 5 ∧ acceleratedOrbit 13 5844 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5844 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5844) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5844.1, data_13_5844.2]

/-- Complete interval computation for depth 13, residue 5845. -/
theorem bounds_13_5845 : exactInterval 13 5845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5845 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5845) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5845 : oddCount 5845 13 = 5 ∧ acceleratedOrbit 13 5845 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5845 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5845) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5845.1, data_13_5845.2]

/-- Complete interval computation for depth 13, residue 5846. -/
theorem bounds_13_5846 : exactInterval 13 5846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5846 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5846) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5846 : oddCount 5846 13 = 6 ∧ acceleratedOrbit 13 5846 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5846 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5846) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5846.1, data_13_5846.2]

/-- Complete interval computation for depth 13, residue 5847. -/
theorem bounds_13_5847 : exactInterval 13 5847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5847 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5847) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5847 : oddCount 5847 13 = 6 ∧ acceleratedOrbit 13 5847 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5847 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5847) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5847.1, data_13_5847.2]

/-- Complete interval computation for depth 13, residue 5848. -/
theorem bounds_13_5848 : exactInterval 13 5848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5848 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5848) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5848 : oddCount 5848 13 = 7 ∧ acceleratedOrbit 13 5848 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5848 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5848) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5848.1, data_13_5848.2]

/-- Complete interval computation for depth 13, residue 5849. -/
theorem bounds_13_5849 : exactInterval 13 5849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5849 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5849) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5849 : oddCount 5849 13 = 7 ∧ acceleratedOrbit 13 5849 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5849 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5849) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5849.1, data_13_5849.2]

/-- Complete interval computation for depth 13, residue 5850. -/
theorem bounds_13_5850 : exactInterval 13 5850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5850 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5850) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5850 : oddCount 5850 13 = 7 ∧ acceleratedOrbit 13 5850 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5850 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5850) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5850.1, data_13_5850.2]

/-- Complete interval computation for depth 13, residue 5851. -/
theorem bounds_13_5851 : exactInterval 13 5851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5851 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5851) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5851 : oddCount 5851 13 = 8 ∧ acceleratedOrbit 13 5851 = 4688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5851 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5851) = 3 ^ 8 * m + 4688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5851.1, data_13_5851.2]

/-- Complete interval computation for depth 13, residue 5852. -/
theorem bounds_13_5852 : exactInterval 13 5852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5852 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5852) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5852 : oddCount 5852 13 = 7 ∧ acceleratedOrbit 13 5852 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5852 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5852) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5852.1, data_13_5852.2]

/-- Complete interval computation for depth 13, residue 5853. -/
theorem bounds_13_5853 : exactInterval 13 5853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5853 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5853) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5853 : oddCount 5853 13 = 7 ∧ acceleratedOrbit 13 5853 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5853 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5853) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5853.1, data_13_5853.2]

/-- Complete interval computation for depth 13, residue 5854. -/
theorem bounds_13_5854 : exactInterval 13 5854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5854 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5854) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5854 : oddCount 5854 13 = 8 ∧ acceleratedOrbit 13 5854 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5854 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5854) = 3 ^ 8 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5854.1, data_13_5854.2]

/-- Complete interval computation for depth 13, residue 5855. -/
theorem bounds_13_5855 : exactInterval 13 5855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5855 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5855) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5855 : oddCount 5855 13 = 8 ∧ acceleratedOrbit 13 5855 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5855 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5855) = 3 ^ 8 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5855.1, data_13_5855.2]

/-- Complete interval computation for depth 13, residue 5856. -/
theorem bounds_13_5856 : exactInterval 13 5856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5856 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5856) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5856 : oddCount 5856 13 = 5 ∧ acceleratedOrbit 13 5856 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5856 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5856) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5856.1, data_13_5856.2]

end Collatz.Research.StoppingAtlas.Batch0848
