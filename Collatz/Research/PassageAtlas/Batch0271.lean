import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0271

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8847. -/
theorem bounds_15_8847 : exactInterval 15 8847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8847 : oddCount 8847 15 = 10 ∧ acceleratedOrbit 15 8847 = 15947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8847) = 3 ^ 10 * m + 15947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8847.1, data_15_8847.2]

/-- Complete interval computation for depth 15, residue 8848. -/
theorem bounds_15_8848 : exactInterval 15 8848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8848 : oddCount 8848 15 = 8 ∧ acceleratedOrbit 15 8848 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8848) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8848.1, data_15_8848.2]

/-- Complete interval computation for depth 15, residue 8849. -/
theorem bounds_15_8849 : exactInterval 15 8849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8849 : oddCount 8849 15 = 6 ∧ acceleratedOrbit 15 8849 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8849) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8849.1, data_15_8849.2]

/-- Complete interval computation for depth 15, residue 8850. -/
theorem bounds_15_8850 : exactInterval 15 8850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8850 : oddCount 8850 15 = 6 ∧ acceleratedOrbit 15 8850 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8850) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8850.1, data_15_8850.2]

/-- Complete interval computation for depth 15, residue 8851. -/
theorem bounds_15_8851 : exactInterval 15 8851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8851 : oddCount 8851 15 = 6 ∧ acceleratedOrbit 15 8851 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8851) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8851.1, data_15_8851.2]

/-- Complete interval computation for depth 15, residue 8852. -/
theorem bounds_15_8852 : exactInterval 15 8852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8852 : oddCount 8852 15 = 8 ∧ acceleratedOrbit 15 8852 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8852) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8852.1, data_15_8852.2]

/-- Complete interval computation for depth 15, residue 8853. -/
theorem bounds_15_8853 : exactInterval 15 8853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8853 : oddCount 8853 15 = 8 ∧ acceleratedOrbit 15 8853 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8853) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8853.1, data_15_8853.2]

/-- Complete interval computation for depth 15, residue 8854. -/
theorem bounds_15_8854 : exactInterval 15 8854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8854 : oddCount 8854 15 = 7 ∧ acceleratedOrbit 15 8854 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8854) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8854.1, data_15_8854.2]

/-- Complete interval computation for depth 15, residue 8855. -/
theorem bounds_15_8855 : exactInterval 15 8855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8855 : oddCount 8855 15 = 7 ∧ acceleratedOrbit 15 8855 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8855) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8855.1, data_15_8855.2]

/-- Complete interval computation for depth 15, residue 8856. -/
theorem bounds_15_8856 : exactInterval 15 8856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8856 : oddCount 8856 15 = 8 ∧ acceleratedOrbit 15 8856 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8856) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8856.1, data_15_8856.2]

/-- Complete interval computation for depth 15, residue 8857. -/
theorem bounds_15_8857 : exactInterval 15 8857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8857 : oddCount 8857 15 = 8 ∧ acceleratedOrbit 15 8857 = 1775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8857) = 3 ^ 8 * m + 1775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8857.1, data_15_8857.2]

/-- Complete interval computation for depth 15, residue 8858. -/
theorem bounds_15_8858 : exactInterval 15 8858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8858 : oddCount 8858 15 = 8 ∧ acceleratedOrbit 15 8858 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8858) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8858.1, data_15_8858.2]

/-- Complete interval computation for depth 15, residue 8859. -/
theorem bounds_15_8859 : exactInterval 15 8859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8859 : oddCount 8859 15 = 10 ∧ acceleratedOrbit 15 8859 = 15967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8859) = 3 ^ 10 * m + 15967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8859.1, data_15_8859.2]

/-- Complete interval computation for depth 15, residue 8860. -/
theorem bounds_15_8860 : exactInterval 15 8860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8860 : oddCount 8860 15 = 10 ∧ acceleratedOrbit 15 8860 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8860) = 3 ^ 10 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8860.1, data_15_8860.2]

/-- Complete interval computation for depth 15, residue 8861. -/
theorem bounds_15_8861 : exactInterval 15 8861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8861 : oddCount 8861 15 = 10 ∧ acceleratedOrbit 15 8861 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8861) = 3 ^ 10 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8861.1, data_15_8861.2]

/-- Complete interval computation for depth 15, residue 8862. -/
theorem bounds_15_8862 : exactInterval 15 8862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8862 : oddCount 8862 15 = 10 ∧ acceleratedOrbit 15 8862 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8862) = 3 ^ 10 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8862.1, data_15_8862.2]

/-- Complete interval computation for depth 15, residue 8863. -/
theorem bounds_15_8863 : exactInterval 15 8863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8863 : oddCount 8863 15 = 10 ∧ acceleratedOrbit 15 8863 = 15974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8863) = 3 ^ 10 * m + 15974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8863.1, data_15_8863.2]

/-- Complete interval computation for depth 15, residue 8864. -/
theorem bounds_15_8864 : exactInterval 15 8864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8864 : oddCount 8864 15 = 3 ∧ acceleratedOrbit 15 8864 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8864) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8864.1, data_15_8864.2]

/-- Complete interval computation for depth 15, residue 8865. -/
theorem bounds_15_8865 : exactInterval 15 8865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8865 : oddCount 8865 15 = 10 ∧ acceleratedOrbit 15 8865 = 15983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8865) = 3 ^ 10 * m + 15983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8865.1, data_15_8865.2]

/-- Complete interval computation for depth 15, residue 8866. -/
theorem bounds_15_8866 : exactInterval 15 8866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8866 : oddCount 8866 15 = 8 ∧ acceleratedOrbit 15 8866 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8866) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8866.1, data_15_8866.2]

/-- Complete interval computation for depth 15, residue 8867. -/
theorem bounds_15_8867 : exactInterval 15 8867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8867 : oddCount 8867 15 = 8 ∧ acceleratedOrbit 15 8867 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8867) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8867.1, data_15_8867.2]

/-- Complete interval computation for depth 15, residue 8868. -/
theorem bounds_15_8868 : exactInterval 15 8868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8868 : oddCount 8868 15 = 11 ∧ acceleratedOrbit 15 8868 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8868) = 3 ^ 11 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8868.1, data_15_8868.2]

/-- Complete interval computation for depth 15, residue 8869. -/
theorem bounds_15_8869 : exactInterval 15 8869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8869 : oddCount 8869 15 = 11 ∧ acceleratedOrbit 15 8869 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8869) = 3 ^ 11 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8869.1, data_15_8869.2]

/-- Complete interval computation for depth 15, residue 8870. -/
theorem bounds_15_8870 : exactInterval 15 8870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8870 : oddCount 8870 15 = 11 ∧ acceleratedOrbit 15 8870 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8870) = 3 ^ 11 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8870.1, data_15_8870.2]

/-- Complete interval computation for depth 15, residue 8871. -/
theorem bounds_15_8871 : exactInterval 15 8871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8871 : oddCount 8871 15 = 9 ∧ acceleratedOrbit 15 8871 = 5330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8871) = 3 ^ 9 * m + 5330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8871.1, data_15_8871.2]

/-- Complete interval computation for depth 15, residue 8872. -/
theorem bounds_15_8872 : exactInterval 15 8872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8872 : oddCount 8872 15 = 3 ∧ acceleratedOrbit 15 8872 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8872) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8872.1, data_15_8872.2]

/-- Complete interval computation for depth 15, residue 8873. -/
theorem bounds_15_8873 : exactInterval 15 8873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8873 : oddCount 8873 15 = 12 ∧ acceleratedOrbit 15 8873 = 143932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8873) = 3 ^ 12 * m + 143932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8873.1, data_15_8873.2]

/-- Complete interval computation for depth 15, residue 8874. -/
theorem bounds_15_8874 : exactInterval 15 8874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8874 : oddCount 8874 15 = 3 ∧ acceleratedOrbit 15 8874 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8874) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8874.1, data_15_8874.2]

/-- Complete interval computation for depth 15, residue 8875. -/
theorem bounds_15_8875 : exactInterval 15 8875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8875 : oddCount 8875 15 = 7 ∧ acceleratedOrbit 15 8875 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8875) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8875.1, data_15_8875.2]

/-- Complete interval computation for depth 15, residue 8876. -/
theorem bounds_15_8876 : exactInterval 15 8876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8876 : oddCount 8876 15 = 8 ∧ acceleratedOrbit 15 8876 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8876) = 3 ^ 8 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8876.1, data_15_8876.2]

/-- Complete interval computation for depth 15, residue 8877. -/
theorem bounds_15_8877 : exactInterval 15 8877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8877 : oddCount 8877 15 = 8 ∧ acceleratedOrbit 15 8877 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8877) = 3 ^ 8 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8877.1, data_15_8877.2]

/-- Complete interval computation for depth 15, residue 8878. -/
theorem bounds_15_8878 : exactInterval 15 8878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8878 : oddCount 8878 15 = 8 ∧ acceleratedOrbit 15 8878 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8878) = 3 ^ 8 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8878.1, data_15_8878.2]

/-- Complete interval computation for depth 15, residue 8879. -/
theorem bounds_15_8879 : exactInterval 15 8879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8879 : oddCount 8879 15 = 9 ∧ acceleratedOrbit 15 8879 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8879) = 3 ^ 9 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8879.1, data_15_8879.2]

end Collatz.Research.PassageAtlas.Batch0271
