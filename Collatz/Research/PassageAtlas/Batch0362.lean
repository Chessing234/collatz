import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0362

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11829. -/
theorem bounds_15_11829 : exactInterval 15 11829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11829 : oddCount 11829 15 = 3 ∧ acceleratedOrbit 15 11829 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11829) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11829.1, data_15_11829.2]

/-- Complete interval computation for depth 15, residue 11830. -/
theorem bounds_15_11830 : exactInterval 15 11830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11830 : oddCount 11830 15 = 12 ∧ acceleratedOrbit 15 11830 = 191909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11830) = 3 ^ 12 * m + 191909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11830.1, data_15_11830.2]

/-- Complete interval computation for depth 15, residue 11831. -/
theorem bounds_15_11831 : exactInterval 15 11831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11831 : oddCount 11831 15 = 12 ∧ acceleratedOrbit 15 11831 = 191909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11831) = 3 ^ 12 * m + 191909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11831.1, data_15_11831.2]

/-- Complete interval computation for depth 15, residue 11832. -/
theorem bounds_15_11832 : exactInterval 15 11832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11832 : oddCount 11832 15 = 7 ∧ acceleratedOrbit 15 11832 = 791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11832) = 3 ^ 7 * m + 791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11832.1, data_15_11832.2]

/-- Complete interval computation for depth 15, residue 11833. -/
theorem bounds_15_11833 : exactInterval 15 11833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11833 : oddCount 11833 15 = 7 ∧ acceleratedOrbit 15 11833 = 790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11833) = 3 ^ 7 * m + 790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11833.1, data_15_11833.2]

/-- Complete interval computation for depth 15, residue 11834. -/
theorem bounds_15_11834 : exactInterval 15 11834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11834 : oddCount 11834 15 = 7 ∧ acceleratedOrbit 15 11834 = 791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11834) = 3 ^ 7 * m + 791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11834.1, data_15_11834.2]

/-- Complete interval computation for depth 15, residue 11835. -/
theorem bounds_15_11835 : exactInterval 15 11835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11835 : oddCount 11835 15 = 8 ∧ acceleratedOrbit 15 11835 = 2371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11835) = 3 ^ 8 * m + 2371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11835.1, data_15_11835.2]

/-- Complete interval computation for depth 15, residue 11836. -/
theorem bounds_15_11836 : exactInterval 15 11836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11836 : oddCount 11836 15 = 7 ∧ acceleratedOrbit 15 11836 = 791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11836) = 3 ^ 7 * m + 791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11836.1, data_15_11836.2]

/-- Complete interval computation for depth 15, residue 11837. -/
theorem bounds_15_11837 : exactInterval 15 11837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11837 : oddCount 11837 15 = 7 ∧ acceleratedOrbit 15 11837 = 791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11837) = 3 ^ 7 * m + 791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11837.1, data_15_11837.2]

/-- Complete interval computation for depth 15, residue 11838. -/
theorem bounds_15_11838 : exactInterval 15 11838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11838 : oddCount 11838 15 = 8 ∧ acceleratedOrbit 15 11838 = 2371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11838) = 3 ^ 8 * m + 2371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11838.1, data_15_11838.2]

/-- Complete interval computation for depth 15, residue 11839. -/
theorem bounds_15_11839 : exactInterval 15 11839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11839 : oddCount 11839 15 = 8 ∧ acceleratedOrbit 15 11839 = 2371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11839) = 3 ^ 8 * m + 2371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11839.1, data_15_11839.2]

/-- Complete interval computation for depth 15, residue 11840. -/
theorem bounds_15_11840 : exactInterval 15 11840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11840 : oddCount 11840 15 = 5 ∧ acceleratedOrbit 15 11840 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11840) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11840.1, data_15_11840.2]

/-- Complete interval computation for depth 15, residue 11841. -/
theorem bounds_15_11841 : exactInterval 15 11841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11841 : oddCount 11841 15 = 8 ∧ acceleratedOrbit 15 11841 = 2375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11841) = 3 ^ 8 * m + 2375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11841.1, data_15_11841.2]

/-- Complete interval computation for depth 15, residue 11842. -/
theorem bounds_15_11842 : exactInterval 15 11842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11842 : oddCount 11842 15 = 8 ∧ acceleratedOrbit 15 11842 = 2375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11842) = 3 ^ 8 * m + 2375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11842.1, data_15_11842.2]

/-- Complete interval computation for depth 15, residue 11843. -/
theorem bounds_15_11843 : exactInterval 15 11843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11843 : oddCount 11843 15 = 8 ∧ acceleratedOrbit 15 11843 = 2375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11843) = 3 ^ 8 * m + 2375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11843.1, data_15_11843.2]

/-- Complete interval computation for depth 15, residue 11844. -/
theorem bounds_15_11844 : exactInterval 15 11844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11844 : oddCount 11844 15 = 5 ∧ acceleratedOrbit 15 11844 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11844) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11844.1, data_15_11844.2]

/-- Complete interval computation for depth 15, residue 11845. -/
theorem bounds_15_11845 : exactInterval 15 11845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11845 : oddCount 11845 15 = 5 ∧ acceleratedOrbit 15 11845 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11845) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11845.1, data_15_11845.2]

/-- Complete interval computation for depth 15, residue 11846. -/
theorem bounds_15_11846 : exactInterval 15 11846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11846 : oddCount 11846 15 = 5 ∧ acceleratedOrbit 15 11846 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11846) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11846.1, data_15_11846.2]

/-- Complete interval computation for depth 15, residue 11847. -/
theorem bounds_15_11847 : exactInterval 15 11847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11847 : oddCount 11847 15 = 9 ∧ acceleratedOrbit 15 11847 = 7118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11847) = 3 ^ 9 * m + 7118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11847.1, data_15_11847.2]

/-- Complete interval computation for depth 15, residue 11848. -/
theorem bounds_15_11848 : exactInterval 15 11848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11848 : oddCount 11848 15 = 5 ∧ acceleratedOrbit 15 11848 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11848) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11848.1, data_15_11848.2]

/-- Complete interval computation for depth 15, residue 11849. -/
theorem bounds_15_11849 : exactInterval 15 11849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11849 : oddCount 11849 15 = 7 ∧ acceleratedOrbit 15 11849 = 791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11849) = 3 ^ 7 * m + 791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11849.1, data_15_11849.2]

/-- Complete interval computation for depth 15, residue 11850. -/
theorem bounds_15_11850 : exactInterval 15 11850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11850 : oddCount 11850 15 = 5 ∧ acceleratedOrbit 15 11850 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11850) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11850.1, data_15_11850.2]

/-- Complete interval computation for depth 15, residue 11851. -/
theorem bounds_15_11851 : exactInterval 15 11851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11851 : oddCount 11851 15 = 5 ∧ acceleratedOrbit 15 11851 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11851) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11851.1, data_15_11851.2]

/-- Complete interval computation for depth 15, residue 11852. -/
theorem bounds_15_11852 : exactInterval 15 11852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11852 : oddCount 11852 15 = 5 ∧ acceleratedOrbit 15 11852 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11852) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11852.1, data_15_11852.2]

/-- Complete interval computation for depth 15, residue 11853. -/
theorem bounds_15_11853 : exactInterval 15 11853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11853 : oddCount 11853 15 = 5 ∧ acceleratedOrbit 15 11853 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11853) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11853.1, data_15_11853.2]

/-- Complete interval computation for depth 15, residue 11854. -/
theorem bounds_15_11854 : exactInterval 15 11854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11854 : oddCount 11854 15 = 9 ∧ acceleratedOrbit 15 11854 = 7123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11854) = 3 ^ 9 * m + 7123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11854.1, data_15_11854.2]

/-- Complete interval computation for depth 15, residue 11855. -/
theorem bounds_15_11855 : exactInterval 15 11855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11855 : oddCount 11855 15 = 9 ∧ acceleratedOrbit 15 11855 = 7123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11855) = 3 ^ 9 * m + 7123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11855.1, data_15_11855.2]

/-- Complete interval computation for depth 15, residue 11856. -/
theorem bounds_15_11856 : exactInterval 15 11856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11856 : oddCount 11856 15 = 5 ∧ acceleratedOrbit 15 11856 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11856) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11856.1, data_15_11856.2]

/-- Complete interval computation for depth 15, residue 11857. -/
theorem bounds_15_11857 : exactInterval 15 11857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11857 : oddCount 11857 15 = 9 ∧ acceleratedOrbit 15 11857 = 7127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11857) = 3 ^ 9 * m + 7127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11857.1, data_15_11857.2]

/-- Complete interval computation for depth 15, residue 11858. -/
theorem bounds_15_11858 : exactInterval 15 11858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11858 : oddCount 11858 15 = 9 ∧ acceleratedOrbit 15 11858 = 7127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11858) = 3 ^ 9 * m + 7127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11858.1, data_15_11858.2]

/-- Complete interval computation for depth 15, residue 11859. -/
theorem bounds_15_11859 : exactInterval 15 11859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11859 : oddCount 11859 15 = 9 ∧ acceleratedOrbit 15 11859 = 7127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11859) = 3 ^ 9 * m + 7127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11859.1, data_15_11859.2]

/-- Complete interval computation for depth 15, residue 11860. -/
theorem bounds_15_11860 : exactInterval 15 11860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11860 : oddCount 11860 15 = 5 ∧ acceleratedOrbit 15 11860 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11860) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11860.1, data_15_11860.2]

/-- Complete interval computation for depth 15, residue 11861. -/
theorem bounds_15_11861 : exactInterval 15 11861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11861 : oddCount 11861 15 = 5 ∧ acceleratedOrbit 15 11861 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11861) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11861.1, data_15_11861.2]

end Collatz.Research.PassageAtlas.Batch0362
