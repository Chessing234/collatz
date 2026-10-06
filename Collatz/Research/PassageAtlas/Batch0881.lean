import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0881

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28835. -/
theorem bounds_15_28835 : exactInterval 15 28835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28835 : oddCount 28835 15 = 8 ∧ acceleratedOrbit 15 28835 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28835) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28835.1, data_15_28835.2]

/-- Complete interval computation for depth 15, residue 28836. -/
theorem bounds_15_28836 : exactInterval 15 28836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28836 : oddCount 28836 15 = 7 ∧ acceleratedOrbit 15 28836 = 1925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28836) = 3 ^ 7 * m + 1925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28836.1, data_15_28836.2]

/-- Complete interval computation for depth 15, residue 28837. -/
theorem bounds_15_28837 : exactInterval 15 28837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28837 : oddCount 28837 15 = 7 ∧ acceleratedOrbit 15 28837 = 1925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28837) = 3 ^ 7 * m + 1925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28837.1, data_15_28837.2]

/-- Complete interval computation for depth 15, residue 28838. -/
theorem bounds_15_28838 : exactInterval 15 28838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28838 : oddCount 28838 15 = 7 ∧ acceleratedOrbit 15 28838 = 1925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28838) = 3 ^ 7 * m + 1925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28838.1, data_15_28838.2]

/-- Complete interval computation for depth 15, residue 28839. -/
theorem bounds_15_28839 : exactInterval 15 28839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28839 : oddCount 28839 15 = 11 ∧ acceleratedOrbit 15 28839 = 155915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28839) = 3 ^ 11 * m + 155915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28839.1, data_15_28839.2]

/-- Complete interval computation for depth 15, residue 28840. -/
theorem bounds_15_28840 : exactInterval 15 28840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28840 : oddCount 28840 15 = 6 ∧ acceleratedOrbit 15 28840 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28840) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28840.1, data_15_28840.2]

/-- Complete interval computation for depth 15, residue 28841. -/
theorem bounds_15_28841 : exactInterval 15 28841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28841 : oddCount 28841 15 = 11 ∧ acceleratedOrbit 15 28841 = 155927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28841) = 3 ^ 11 * m + 155927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28841.1, data_15_28841.2]

/-- Complete interval computation for depth 15, residue 28842. -/
theorem bounds_15_28842 : exactInterval 15 28842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28842 : oddCount 28842 15 = 6 ∧ acceleratedOrbit 15 28842 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28842) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28842.1, data_15_28842.2]

/-- Complete interval computation for depth 15, residue 28843. -/
theorem bounds_15_28843 : exactInterval 15 28843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28843 : oddCount 28843 15 = 8 ∧ acceleratedOrbit 15 28843 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28843) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28843.1, data_15_28843.2]

/-- Complete interval computation for depth 15, residue 28844. -/
theorem bounds_15_28844 : exactInterval 15 28844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28844 : oddCount 28844 15 = 5 ∧ acceleratedOrbit 15 28844 = 214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28844) = 3 ^ 5 * m + 214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28844.1, data_15_28844.2]

/-- Complete interval computation for depth 15, residue 28845. -/
theorem bounds_15_28845 : exactInterval 15 28845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28845 : oddCount 28845 15 = 5 ∧ acceleratedOrbit 15 28845 = 214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28845) = 3 ^ 5 * m + 214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28845.1, data_15_28845.2]

/-- Complete interval computation for depth 15, residue 28846. -/
theorem bounds_15_28846 : exactInterval 15 28846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28846 : oddCount 28846 15 = 5 ∧ acceleratedOrbit 15 28846 = 214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28846) = 3 ^ 5 * m + 214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28846.1, data_15_28846.2]

/-- Complete interval computation for depth 15, residue 28847. -/
theorem bounds_15_28847 : exactInterval 15 28847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28847 : oddCount 28847 15 = 9 ∧ acceleratedOrbit 15 28847 = 17329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28847) = 3 ^ 9 * m + 17329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28847.1, data_15_28847.2]

/-- Complete interval computation for depth 15, residue 28848. -/
theorem bounds_15_28848 : exactInterval 15 28848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28848 : oddCount 28848 15 = 6 ∧ acceleratedOrbit 15 28848 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28848) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28848.1, data_15_28848.2]

/-- Complete interval computation for depth 15, residue 28849. -/
theorem bounds_15_28849 : exactInterval 15 28849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28849 : oddCount 28849 15 = 5 ∧ acceleratedOrbit 15 28849 = 214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28849) = 3 ^ 5 * m + 214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28849.1, data_15_28849.2]

/-- Complete interval computation for depth 15, residue 28850. -/
theorem bounds_15_28850 : exactInterval 15 28850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28850 : oddCount 28850 15 = 5 ∧ acceleratedOrbit 15 28850 = 214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28850) = 3 ^ 5 * m + 214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28850.1, data_15_28850.2]

/-- Complete interval computation for depth 15, residue 28851. -/
theorem bounds_15_28851 : exactInterval 15 28851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28851 : oddCount 28851 15 = 5 ∧ acceleratedOrbit 15 28851 = 214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28851) = 3 ^ 5 * m + 214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28851.1, data_15_28851.2]

/-- Complete interval computation for depth 15, residue 28852. -/
theorem bounds_15_28852 : exactInterval 15 28852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28852 : oddCount 28852 15 = 6 ∧ acceleratedOrbit 15 28852 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28852) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28852.1, data_15_28852.2]

/-- Complete interval computation for depth 15, residue 28853. -/
theorem bounds_15_28853 : exactInterval 15 28853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28853 : oddCount 28853 15 = 6 ∧ acceleratedOrbit 15 28853 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28853) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28853.1, data_15_28853.2]

/-- Complete interval computation for depth 15, residue 28854. -/
theorem bounds_15_28854 : exactInterval 15 28854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28854 : oddCount 28854 15 = 12 ∧ acceleratedOrbit 15 28854 = 468017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28854) = 3 ^ 12 * m + 468017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28854.1, data_15_28854.2]

/-- Complete interval computation for depth 15, residue 28855. -/
theorem bounds_15_28855 : exactInterval 15 28855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28855 : oddCount 28855 15 = 12 ∧ acceleratedOrbit 15 28855 = 468017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28855) = 3 ^ 12 * m + 468017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28855.1, data_15_28855.2]

/-- Complete interval computation for depth 15, residue 28856. -/
theorem bounds_15_28856 : exactInterval 15 28856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28856 : oddCount 28856 15 = 6 ∧ acceleratedOrbit 15 28856 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28856) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28856.1, data_15_28856.2]

/-- Complete interval computation for depth 15, residue 28857. -/
theorem bounds_15_28857 : exactInterval 15 28857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28857 : oddCount 28857 15 = 8 ∧ acceleratedOrbit 15 28857 = 5779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28857) = 3 ^ 8 * m + 5779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28857.1, data_15_28857.2]

/-- Complete interval computation for depth 15, residue 28858. -/
theorem bounds_15_28858 : exactInterval 15 28858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28858 : oddCount 28858 15 = 6 ∧ acceleratedOrbit 15 28858 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28858) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28858.1, data_15_28858.2]

/-- Complete interval computation for depth 15, residue 28859. -/
theorem bounds_15_28859 : exactInterval 15 28859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28859 : oddCount 28859 15 = 8 ∧ acceleratedOrbit 15 28859 = 5779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28859) = 3 ^ 8 * m + 5779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28859.1, data_15_28859.2]

/-- Complete interval computation for depth 15, residue 28860. -/
theorem bounds_15_28860 : exactInterval 15 28860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28860 : oddCount 28860 15 = 8 ∧ acceleratedOrbit 15 28860 = 5780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28860) = 3 ^ 8 * m + 5780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28860.1, data_15_28860.2]

/-- Complete interval computation for depth 15, residue 28861. -/
theorem bounds_15_28861 : exactInterval 15 28861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28861 : oddCount 28861 15 = 8 ∧ acceleratedOrbit 15 28861 = 5780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28861) = 3 ^ 8 * m + 5780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28861.1, data_15_28861.2]

/-- Complete interval computation for depth 15, residue 28862. -/
theorem bounds_15_28862 : exactInterval 15 28862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28862 : oddCount 28862 15 = 8 ∧ acceleratedOrbit 15 28862 = 5780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28862) = 3 ^ 8 * m + 5780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28862.1, data_15_28862.2]

/-- Complete interval computation for depth 15, residue 28863. -/
theorem bounds_15_28863 : exactInterval 15 28863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28863 : oddCount 28863 15 = 10 ∧ acceleratedOrbit 15 28863 = 52015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28863) = 3 ^ 10 * m + 52015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28863.1, data_15_28863.2]

/-- Complete interval computation for depth 15, residue 28864. -/
theorem bounds_15_28864 : exactInterval 15 28864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28864 : oddCount 28864 15 = 6 ∧ acceleratedOrbit 15 28864 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28864) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28864.1, data_15_28864.2]

/-- Complete interval computation for depth 15, residue 28865. -/
theorem bounds_15_28865 : exactInterval 15 28865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28865 : oddCount 28865 15 = 7 ∧ acceleratedOrbit 15 28865 = 1927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28865) = 3 ^ 7 * m + 1927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28865.1, data_15_28865.2]

/-- Complete interval computation for depth 15, residue 28866. -/
theorem bounds_15_28866 : exactInterval 15 28866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28866 : oddCount 28866 15 = 7 ∧ acceleratedOrbit 15 28866 = 1927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28866) = 3 ^ 7 * m + 1927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28866.1, data_15_28866.2]

/-- Complete interval computation for depth 15, residue 28867. -/
theorem bounds_15_28867 : exactInterval 15 28867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28867 : oddCount 28867 15 = 7 ∧ acceleratedOrbit 15 28867 = 1927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28867) = 3 ^ 7 * m + 1927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28867.1, data_15_28867.2]

end Collatz.Research.PassageAtlas.Batch0881
