import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0179

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5832. -/
theorem bounds_15_5832 : exactInterval 15 5832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5832 : oddCount 5832 15 = 5 ∧ acceleratedOrbit 15 5832 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5832) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5832.1, data_15_5832.2]

/-- Complete interval computation for depth 15, residue 5833. -/
theorem bounds_15_5833 : exactInterval 15 5833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5833 : oddCount 5833 15 = 9 ∧ acceleratedOrbit 15 5833 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5833) = 3 ^ 9 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5833.1, data_15_5833.2]

/-- Complete interval computation for depth 15, residue 5834. -/
theorem bounds_15_5834 : exactInterval 15 5834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5834 : oddCount 5834 15 = 5 ∧ acceleratedOrbit 15 5834 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5834) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5834.1, data_15_5834.2]

/-- Complete interval computation for depth 15, residue 5835. -/
theorem bounds_15_5835 : exactInterval 15 5835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5835 : oddCount 5835 15 = 9 ∧ acceleratedOrbit 15 5835 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5835) = 3 ^ 9 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5835.1, data_15_5835.2]

/-- Complete interval computation for depth 15, residue 5836. -/
theorem bounds_15_5836 : exactInterval 15 5836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5836 : oddCount 5836 15 = 5 ∧ acceleratedOrbit 15 5836 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5836) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5836.1, data_15_5836.2]

/-- Complete interval computation for depth 15, residue 5837. -/
theorem bounds_15_5837 : exactInterval 15 5837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5837 : oddCount 5837 15 = 5 ∧ acceleratedOrbit 15 5837 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5837) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5837.1, data_15_5837.2]

/-- Complete interval computation for depth 15, residue 5838. -/
theorem bounds_15_5838 : exactInterval 15 5838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5838 : oddCount 5838 15 = 10 ∧ acceleratedOrbit 15 5838 = 10525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5838) = 3 ^ 10 * m + 10525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5838.1, data_15_5838.2]

/-- Complete interval computation for depth 15, residue 5839. -/
theorem bounds_15_5839 : exactInterval 15 5839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5839 : oddCount 5839 15 = 10 ∧ acceleratedOrbit 15 5839 = 10525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5839) = 3 ^ 10 * m + 10525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5839.1, data_15_5839.2]

/-- Complete interval computation for depth 15, residue 5840. -/
theorem bounds_15_5840 : exactInterval 15 5840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5840 : oddCount 5840 15 = 7 ∧ acceleratedOrbit 15 5840 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5840) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5840.1, data_15_5840.2]

/-- Complete interval computation for depth 15, residue 5841. -/
theorem bounds_15_5841 : exactInterval 15 5841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5841 : oddCount 5841 15 = 8 ∧ acceleratedOrbit 15 5841 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5841) = 3 ^ 8 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5841.1, data_15_5841.2]

/-- Complete interval computation for depth 15, residue 5842. -/
theorem bounds_15_5842 : exactInterval 15 5842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5842 : oddCount 5842 15 = 8 ∧ acceleratedOrbit 15 5842 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5842) = 3 ^ 8 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5842.1, data_15_5842.2]

/-- Complete interval computation for depth 15, residue 5843. -/
theorem bounds_15_5843 : exactInterval 15 5843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5843 : oddCount 5843 15 = 8 ∧ acceleratedOrbit 15 5843 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5843) = 3 ^ 8 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5843.1, data_15_5843.2]

/-- Complete interval computation for depth 15, residue 5844. -/
theorem bounds_15_5844 : exactInterval 15 5844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5844 : oddCount 5844 15 = 7 ∧ acceleratedOrbit 15 5844 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5844) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5844.1, data_15_5844.2]

/-- Complete interval computation for depth 15, residue 5845. -/
theorem bounds_15_5845 : exactInterval 15 5845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5845 : oddCount 5845 15 = 7 ∧ acceleratedOrbit 15 5845 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5845) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5845.1, data_15_5845.2]

/-- Complete interval computation for depth 15, residue 5846. -/
theorem bounds_15_5846 : exactInterval 15 5846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5846 : oddCount 5846 15 = 7 ∧ acceleratedOrbit 15 5846 = 391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5846) = 3 ^ 7 * m + 391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5846.1, data_15_5846.2]

/-- Complete interval computation for depth 15, residue 5847. -/
theorem bounds_15_5847 : exactInterval 15 5847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5847 : oddCount 5847 15 = 7 ∧ acceleratedOrbit 15 5847 = 391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5847) = 3 ^ 7 * m + 391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5847.1, data_15_5847.2]

/-- Complete interval computation for depth 15, residue 5848. -/
theorem bounds_15_5848 : exactInterval 15 5848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5848 : oddCount 5848 15 = 8 ∧ acceleratedOrbit 15 5848 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5848) = 3 ^ 8 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5848.1, data_15_5848.2]

/-- Complete interval computation for depth 15, residue 5849. -/
theorem bounds_15_5849 : exactInterval 15 5849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5849 : oddCount 5849 15 = 8 ∧ acceleratedOrbit 15 5849 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5849) = 3 ^ 8 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5849.1, data_15_5849.2]

/-- Complete interval computation for depth 15, residue 5850. -/
theorem bounds_15_5850 : exactInterval 15 5850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5850 : oddCount 5850 15 = 8 ∧ acceleratedOrbit 15 5850 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5850) = 3 ^ 8 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5850.1, data_15_5850.2]

/-- Complete interval computation for depth 15, residue 5851. -/
theorem bounds_15_5851 : exactInterval 15 5851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5851 : oddCount 5851 15 = 8 ∧ acceleratedOrbit 15 5851 = 1172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5851) = 3 ^ 8 * m + 1172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5851.1, data_15_5851.2]

/-- Complete interval computation for depth 15, residue 5852. -/
theorem bounds_15_5852 : exactInterval 15 5852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5852 : oddCount 5852 15 = 8 ∧ acceleratedOrbit 15 5852 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5852) = 3 ^ 8 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5852.1, data_15_5852.2]

/-- Complete interval computation for depth 15, residue 5853. -/
theorem bounds_15_5853 : exactInterval 15 5853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5853 : oddCount 5853 15 = 8 ∧ acceleratedOrbit 15 5853 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5853) = 3 ^ 8 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5853.1, data_15_5853.2]

/-- Complete interval computation for depth 15, residue 5854. -/
theorem bounds_15_5854 : exactInterval 15 5854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5854 : oddCount 5854 15 = 10 ∧ acceleratedOrbit 15 5854 = 10556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5854) = 3 ^ 10 * m + 10556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5854.1, data_15_5854.2]

/-- Complete interval computation for depth 15, residue 5855. -/
theorem bounds_15_5855 : exactInterval 15 5855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5855 : oddCount 5855 15 = 10 ∧ acceleratedOrbit 15 5855 = 10556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5855) = 3 ^ 10 * m + 10556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5855.1, data_15_5855.2]

/-- Complete interval computation for depth 15, residue 5856. -/
theorem bounds_15_5856 : exactInterval 15 5856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5856 : oddCount 5856 15 = 7 ∧ acceleratedOrbit 15 5856 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5856) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5856.1, data_15_5856.2]

/-- Complete interval computation for depth 15, residue 5857. -/
theorem bounds_15_5857 : exactInterval 15 5857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5857 : oddCount 5857 15 = 9 ∧ acceleratedOrbit 15 5857 = 3520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5857) = 3 ^ 9 * m + 3520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5857.1, data_15_5857.2]

/-- Complete interval computation for depth 15, residue 5858. -/
theorem bounds_15_5858 : exactInterval 15 5858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5858 : oddCount 5858 15 = 7 ∧ acceleratedOrbit 15 5858 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5858) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5858.1, data_15_5858.2]

/-- Complete interval computation for depth 15, residue 5859. -/
theorem bounds_15_5859 : exactInterval 15 5859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5859 : oddCount 5859 15 = 7 ∧ acceleratedOrbit 15 5859 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5859) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5859.1, data_15_5859.2]

/-- Complete interval computation for depth 15, residue 5860. -/
theorem bounds_15_5860 : exactInterval 15 5860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5860 : oddCount 5860 15 = 5 ∧ acceleratedOrbit 15 5860 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5860) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5860.1, data_15_5860.2]

/-- Complete interval computation for depth 15, residue 5861. -/
theorem bounds_15_5861 : exactInterval 15 5861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5861 : oddCount 5861 15 = 5 ∧ acceleratedOrbit 15 5861 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5861) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5861.1, data_15_5861.2]

/-- Complete interval computation for depth 15, residue 5862. -/
theorem bounds_15_5862 : exactInterval 15 5862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5862 : oddCount 5862 15 = 5 ∧ acceleratedOrbit 15 5862 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5862) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5862.1, data_15_5862.2]

/-- Complete interval computation for depth 15, residue 5863. -/
theorem bounds_15_5863 : exactInterval 15 5863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5863 : oddCount 5863 15 = 10 ∧ acceleratedOrbit 15 5863 = 10568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5863) = 3 ^ 10 * m + 10568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5863.1, data_15_5863.2]

/-- Complete interval computation for depth 15, residue 5864. -/
theorem bounds_15_5864 : exactInterval 15 5864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5864 : oddCount 5864 15 = 7 ∧ acceleratedOrbit 15 5864 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5864) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5864.1, data_15_5864.2]

end Collatz.Research.PassageAtlas.Batch0179
