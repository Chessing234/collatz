import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0913

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6840. -/
theorem bounds_13_6840 : exactInterval 13 6840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6840 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6840) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6840 : oddCount 6840 13 = 6 ∧ acceleratedOrbit 13 6840 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6840 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6840) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6840.1, data_13_6840.2]

/-- Complete interval computation for depth 13, residue 6841. -/
theorem bounds_13_6841 : exactInterval 13 6841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6841 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6841) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6841 : oddCount 6841 13 = 5 ∧ acceleratedOrbit 13 6841 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6841 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6841) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6841.1, data_13_6841.2]

/-- Complete interval computation for depth 13, residue 6842. -/
theorem bounds_13_6842 : exactInterval 13 6842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6842 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6842) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6842 : oddCount 6842 13 = 6 ∧ acceleratedOrbit 13 6842 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6842 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6842) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6842.1, data_13_6842.2]

/-- Complete interval computation for depth 13, residue 6843. -/
theorem bounds_13_6843 : exactInterval 13 6843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6843 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6843) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6843 : oddCount 6843 13 = 8 ∧ acceleratedOrbit 13 6843 = 5483 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6843 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6843) = 3 ^ 8 * m + 5483 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6843.1, data_13_6843.2]

/-- Complete interval computation for depth 13, residue 6844. -/
theorem bounds_13_6844 : exactInterval 13 6844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6844 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6844) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6844 : oddCount 6844 13 = 7 ∧ acceleratedOrbit 13 6844 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6844 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6844) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6844.1, data_13_6844.2]

/-- Complete interval computation for depth 13, residue 6845. -/
theorem bounds_13_6845 : exactInterval 13 6845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6845 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6845) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6845 : oddCount 6845 13 = 7 ∧ acceleratedOrbit 13 6845 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6845 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6845) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6845.1, data_13_6845.2]

/-- Complete interval computation for depth 13, residue 6846. -/
theorem bounds_13_6846 : exactInterval 13 6846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6846 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6846) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6846 : oddCount 6846 13 = 7 ∧ acceleratedOrbit 13 6846 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6846 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6846) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6846.1, data_13_6846.2]

/-- Complete interval computation for depth 13, residue 6847. -/
theorem bounds_13_6847 : exactInterval 13 6847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6847 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6847) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6847 : oddCount 6847 13 = 9 ∧ acceleratedOrbit 13 6847 = 16454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6847 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6847) = 3 ^ 9 * m + 16454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6847.1, data_13_6847.2]

/-- Complete interval computation for depth 13, residue 6848. -/
theorem bounds_13_6848 : exactInterval 13 6848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6848 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6848) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6848 : oddCount 6848 13 = 5 ∧ acceleratedOrbit 13 6848 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6848 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6848) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6848.1, data_13_6848.2]

/-- Complete interval computation for depth 13, residue 6849. -/
theorem bounds_13_6849 : exactInterval 13 6849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6849 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6849) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6849 : oddCount 6849 13 = 6 ∧ acceleratedOrbit 13 6849 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6849 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6849) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6849.1, data_13_6849.2]

/-- Complete interval computation for depth 13, residue 6850. -/
theorem bounds_13_6850 : exactInterval 13 6850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6850 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6850) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6850 : oddCount 6850 13 = 6 ∧ acceleratedOrbit 13 6850 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6850 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6850) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6850.1, data_13_6850.2]

/-- Complete interval computation for depth 13, residue 6851. -/
theorem bounds_13_6851 : exactInterval 13 6851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6851 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6851) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6851 : oddCount 6851 13 = 6 ∧ acceleratedOrbit 13 6851 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6851 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6851) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6851.1, data_13_6851.2]

/-- Complete interval computation for depth 13, residue 6852. -/
theorem bounds_13_6852 : exactInterval 13 6852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6852 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6852) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6852 : oddCount 6852 13 = 4 ∧ acceleratedOrbit 13 6852 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6852 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6852) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6852.1, data_13_6852.2]

/-- Complete interval computation for depth 13, residue 6853. -/
theorem bounds_13_6853 : exactInterval 13 6853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6853 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6853) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6853 : oddCount 6853 13 = 4 ∧ acceleratedOrbit 13 6853 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6853 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6853) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6853.1, data_13_6853.2]

/-- Complete interval computation for depth 13, residue 6854. -/
theorem bounds_13_6854 : exactInterval 13 6854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6854 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6854) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6854 : oddCount 6854 13 = 4 ∧ acceleratedOrbit 13 6854 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6854 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6854) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6854.1, data_13_6854.2]

end Collatz.Research.StoppingAtlas.Batch0913
