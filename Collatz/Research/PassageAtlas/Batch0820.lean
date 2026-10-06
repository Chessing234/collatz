import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0820

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26836. -/
theorem bounds_15_26836 : exactInterval 15 26836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26836 : oddCount 26836 15 = 4 ∧ acceleratedOrbit 15 26836 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26836) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26836.1, data_15_26836.2]

/-- Complete interval computation for depth 15, residue 26837. -/
theorem bounds_15_26837 : exactInterval 15 26837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26837 : oddCount 26837 15 = 4 ∧ acceleratedOrbit 15 26837 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26837) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26837.1, data_15_26837.2]

/-- Complete interval computation for depth 15, residue 26838. -/
theorem bounds_15_26838 : exactInterval 15 26838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26838 : oddCount 26838 15 = 8 ∧ acceleratedOrbit 15 26838 = 5375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26838) = 3 ^ 8 * m + 5375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26838.1, data_15_26838.2]

/-- Complete interval computation for depth 15, residue 26839. -/
theorem bounds_15_26839 : exactInterval 15 26839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26839 : oddCount 26839 15 = 8 ∧ acceleratedOrbit 15 26839 = 5375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26839) = 3 ^ 8 * m + 5375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26839.1, data_15_26839.2]

/-- Complete interval computation for depth 15, residue 26840. -/
theorem bounds_15_26840 : exactInterval 15 26840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26840 : oddCount 26840 15 = 9 ∧ acceleratedOrbit 15 26840 = 16129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26840) = 3 ^ 9 * m + 16129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26840.1, data_15_26840.2]

/-- Complete interval computation for depth 15, residue 26841. -/
theorem bounds_15_26841 : exactInterval 15 26841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26841 : oddCount 26841 15 = 7 ∧ acceleratedOrbit 15 26841 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26841) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26841.1, data_15_26841.2]

/-- Complete interval computation for depth 15, residue 26842. -/
theorem bounds_15_26842 : exactInterval 15 26842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26842 : oddCount 26842 15 = 9 ∧ acceleratedOrbit 15 26842 = 16129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26842) = 3 ^ 9 * m + 16129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26842.1, data_15_26842.2]

/-- Complete interval computation for depth 15, residue 26843. -/
theorem bounds_15_26843 : exactInterval 15 26843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26843 : oddCount 26843 15 = 10 ∧ acceleratedOrbit 15 26843 = 48377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26843) = 3 ^ 10 * m + 48377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26843.1, data_15_26843.2]

/-- Complete interval computation for depth 15, residue 26844. -/
theorem bounds_15_26844 : exactInterval 15 26844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26844 : oddCount 26844 15 = 9 ∧ acceleratedOrbit 15 26844 = 16129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26844) = 3 ^ 9 * m + 16129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26844.1, data_15_26844.2]

/-- Complete interval computation for depth 15, residue 26845. -/
theorem bounds_15_26845 : exactInterval 15 26845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26845 : oddCount 26845 15 = 9 ∧ acceleratedOrbit 15 26845 = 16129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26845) = 3 ^ 9 * m + 16129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26845.1, data_15_26845.2]

/-- Complete interval computation for depth 15, residue 26846. -/
theorem bounds_15_26846 : exactInterval 15 26846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26846 : oddCount 26846 15 = 10 ∧ acceleratedOrbit 15 26846 = 48383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26846) = 3 ^ 10 * m + 48383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26846.1, data_15_26846.2]

/-- Complete interval computation for depth 15, residue 26847. -/
theorem bounds_15_26847 : exactInterval 15 26847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26847 : oddCount 26847 15 = 10 ∧ acceleratedOrbit 15 26847 = 48383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26847) = 3 ^ 10 * m + 48383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26847.1, data_15_26847.2]

/-- Complete interval computation for depth 15, residue 26848. -/
theorem bounds_15_26848 : exactInterval 15 26848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26848 : oddCount 26848 15 = 7 ∧ acceleratedOrbit 15 26848 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26848) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26848.1, data_15_26848.2]

/-- Complete interval computation for depth 15, residue 26849. -/
theorem bounds_15_26849 : exactInterval 15 26849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26849 : oddCount 26849 15 = 11 ∧ acceleratedOrbit 15 26849 = 145162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26849) = 3 ^ 11 * m + 145162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26849.1, data_15_26849.2]

/-- Complete interval computation for depth 15, residue 26850. -/
theorem bounds_15_26850 : exactInterval 15 26850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26850 : oddCount 26850 15 = 4 ∧ acceleratedOrbit 15 26850 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26850) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26850.1, data_15_26850.2]

/-- Complete interval computation for depth 15, residue 26851. -/
theorem bounds_15_26851 : exactInterval 15 26851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26851 : oddCount 26851 15 = 4 ∧ acceleratedOrbit 15 26851 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26851) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26851.1, data_15_26851.2]

/-- Complete interval computation for depth 15, residue 26852. -/
theorem bounds_15_26852 : exactInterval 15 26852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26852 : oddCount 26852 15 = 7 ∧ acceleratedOrbit 15 26852 = 1793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26852) = 3 ^ 7 * m + 1793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26852.1, data_15_26852.2]

/-- Complete interval computation for depth 15, residue 26853. -/
theorem bounds_15_26853 : exactInterval 15 26853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26853 : oddCount 26853 15 = 7 ∧ acceleratedOrbit 15 26853 = 1793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26853) = 3 ^ 7 * m + 1793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26853.1, data_15_26853.2]

/-- Complete interval computation for depth 15, residue 26854. -/
theorem bounds_15_26854 : exactInterval 15 26854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26854 : oddCount 26854 15 = 7 ∧ acceleratedOrbit 15 26854 = 1793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26854) = 3 ^ 7 * m + 1793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26854.1, data_15_26854.2]

/-- Complete interval computation for depth 15, residue 26855. -/
theorem bounds_15_26855 : exactInterval 15 26855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26855 : oddCount 26855 15 = 10 ∧ acceleratedOrbit 15 26855 = 48397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26855) = 3 ^ 10 * m + 48397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26855.1, data_15_26855.2]

/-- Complete interval computation for depth 15, residue 26856. -/
theorem bounds_15_26856 : exactInterval 15 26856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26856 : oddCount 26856 15 = 7 ∧ acceleratedOrbit 15 26856 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26856) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26856.1, data_15_26856.2]

/-- Complete interval computation for depth 15, residue 26857. -/
theorem bounds_15_26857 : exactInterval 15 26857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26857 : oddCount 26857 15 = 8 ∧ acceleratedOrbit 15 26857 = 5378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26857) = 3 ^ 8 * m + 5378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26857.1, data_15_26857.2]

/-- Complete interval computation for depth 15, residue 26858. -/
theorem bounds_15_26858 : exactInterval 15 26858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26858 : oddCount 26858 15 = 7 ∧ acceleratedOrbit 15 26858 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26858) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26858.1, data_15_26858.2]

/-- Complete interval computation for depth 15, residue 26859. -/
theorem bounds_15_26859 : exactInterval 15 26859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26859 : oddCount 26859 15 = 9 ∧ acceleratedOrbit 15 26859 = 16136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26859) = 3 ^ 9 * m + 16136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26859.1, data_15_26859.2]

/-- Complete interval computation for depth 15, residue 26860. -/
theorem bounds_15_26860 : exactInterval 15 26860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26860 : oddCount 26860 15 = 6 ∧ acceleratedOrbit 15 26860 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26860) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26860.1, data_15_26860.2]

/-- Complete interval computation for depth 15, residue 26861. -/
theorem bounds_15_26861 : exactInterval 15 26861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26861 : oddCount 26861 15 = 6 ∧ acceleratedOrbit 15 26861 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26861) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26861.1, data_15_26861.2]

/-- Complete interval computation for depth 15, residue 26862. -/
theorem bounds_15_26862 : exactInterval 15 26862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26862 : oddCount 26862 15 = 6 ∧ acceleratedOrbit 15 26862 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26862) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26862.1, data_15_26862.2]

/-- Complete interval computation for depth 15, residue 26863. -/
theorem bounds_15_26863 : exactInterval 15 26863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26863 : oddCount 26863 15 = 12 ∧ acceleratedOrbit 15 26863 = 435692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26863) = 3 ^ 12 * m + 435692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26863.1, data_15_26863.2]

/-- Complete interval computation for depth 15, residue 26864. -/
theorem bounds_15_26864 : exactInterval 15 26864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26864 : oddCount 26864 15 = 7 ∧ acceleratedOrbit 15 26864 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26864) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26864.1, data_15_26864.2]

/-- Complete interval computation for depth 15, residue 26865. -/
theorem bounds_15_26865 : exactInterval 15 26865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26865 : oddCount 26865 15 = 7 ∧ acceleratedOrbit 15 26865 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26865) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26865.1, data_15_26865.2]

/-- Complete interval computation for depth 15, residue 26866. -/
theorem bounds_15_26866 : exactInterval 15 26866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26866 : oddCount 26866 15 = 9 ∧ acceleratedOrbit 15 26866 = 16141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26866) = 3 ^ 9 * m + 16141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26866.1, data_15_26866.2]

/-- Complete interval computation for depth 15, residue 26867. -/
theorem bounds_15_26867 : exactInterval 15 26867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26867 : oddCount 26867 15 = 9 ∧ acceleratedOrbit 15 26867 = 16141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26867) = 3 ^ 9 * m + 16141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26867.1, data_15_26867.2]

/-- Complete interval computation for depth 15, residue 26868. -/
theorem bounds_15_26868 : exactInterval 15 26868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26868 : oddCount 26868 15 = 7 ∧ acceleratedOrbit 15 26868 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26868) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26868.1, data_15_26868.2]

end Collatz.Research.PassageAtlas.Batch0820
