import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0978

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7838. -/
theorem bounds_13_7838 : exactInterval 13 7838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7838 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7838) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7838 : oddCount 7838 13 = 8 ∧ acceleratedOrbit 13 7838 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7838 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7838) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7838.1, data_13_7838.2]

/-- Complete interval computation for depth 13, residue 7839. -/
theorem bounds_13_7839 : exactInterval 13 7839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7839 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7839) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7839 : oddCount 7839 13 = 10 ∧ acceleratedOrbit 13 7839 = 56513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7839 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7839) = 3 ^ 10 * m + 56513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7839.1, data_13_7839.2]

/-- Complete interval computation for depth 13, residue 7840. -/
theorem bounds_13_7840 : exactInterval 13 7840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7840 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7840) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7840 : oddCount 7840 13 = 4 ∧ acceleratedOrbit 13 7840 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7840 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7840) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7840.1, data_13_7840.2]

/-- Complete interval computation for depth 13, residue 7841. -/
theorem bounds_13_7841 : exactInterval 13 7841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7841 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7841) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7841 : oddCount 7841 13 = 6 ∧ acceleratedOrbit 13 7841 = 698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7841 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7841) = 3 ^ 6 * m + 698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7841.1, data_13_7841.2]

/-- Complete interval computation for depth 13, residue 7842. -/
theorem bounds_13_7842 : exactInterval 13 7842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7842 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7842) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7842 : oddCount 7842 13 = 7 ∧ acceleratedOrbit 13 7842 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7842 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7842) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7842.1, data_13_7842.2]

/-- Complete interval computation for depth 13, residue 7843. -/
theorem bounds_13_7843 : exactInterval 13 7843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7843 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7843) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7843 : oddCount 7843 13 = 7 ∧ acceleratedOrbit 13 7843 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7843 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7843) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7843.1, data_13_7843.2]

/-- Complete interval computation for depth 13, residue 7844. -/
theorem bounds_13_7844 : exactInterval 13 7844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7844 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7844) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7844 : oddCount 7844 13 = 9 ∧ acceleratedOrbit 13 7844 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7844 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7844) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7844.1, data_13_7844.2]

/-- Complete interval computation for depth 13, residue 7845. -/
theorem bounds_13_7845 : exactInterval 13 7845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7845 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7845) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7845 : oddCount 7845 13 = 9 ∧ acceleratedOrbit 13 7845 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7845 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7845) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7845.1, data_13_7845.2]

/-- Complete interval computation for depth 13, residue 7846. -/
theorem bounds_13_7846 : exactInterval 13 7846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7846 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7846) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7846 : oddCount 7846 13 = 9 ∧ acceleratedOrbit 13 7846 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7846 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7846) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7846.1, data_13_7846.2]

/-- Complete interval computation for depth 13, residue 7847. -/
theorem bounds_13_7847 : exactInterval 13 7847 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7847 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7847) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7847 : oddCount 7847 13 = 8 ∧ acceleratedOrbit 13 7847 = 6286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7847 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7847) = 3 ^ 8 * m + 6286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7847.1, data_13_7847.2]

/-- Complete interval computation for depth 13, residue 7848. -/
theorem bounds_13_7848 : exactInterval 13 7848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7848 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7848) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7848 : oddCount 7848 13 = 4 ∧ acceleratedOrbit 13 7848 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7848 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7848) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7848.1, data_13_7848.2]

/-- Complete interval computation for depth 13, residue 7849. -/
theorem bounds_13_7849 : exactInterval 13 7849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7849 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7849) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7849 : oddCount 7849 13 = 11 ∧ acceleratedOrbit 13 7849 = 169766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7849 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7849) = 3 ^ 11 * m + 169766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7849.1, data_13_7849.2]

/-- Complete interval computation for depth 13, residue 7850. -/
theorem bounds_13_7850 : exactInterval 13 7850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7850 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7850) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7850 : oddCount 7850 13 = 4 ∧ acceleratedOrbit 13 7850 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7850 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7850) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7850.1, data_13_7850.2]

/-- Complete interval computation for depth 13, residue 7851. -/
theorem bounds_13_7851 : exactInterval 13 7851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7851 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7851) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7851 : oddCount 7851 13 = 9 ∧ acceleratedOrbit 13 7851 = 18872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7851 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7851) = 3 ^ 9 * m + 18872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7851.1, data_13_7851.2]

/-- Complete interval computation for depth 13, residue 7852. -/
theorem bounds_13_7852 : exactInterval 13 7852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7852 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7852) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7852 : oddCount 7852 13 = 7 ∧ acceleratedOrbit 13 7852 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7852 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7852) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7852.1, data_13_7852.2]

/-- Complete interval computation for depth 13, residue 7853. -/
theorem bounds_13_7853 : exactInterval 13 7853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7853 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7853) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7853 : oddCount 7853 13 = 7 ∧ acceleratedOrbit 13 7853 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7853 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7853) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7853.1, data_13_7853.2]

end Collatz.Research.StoppingAtlas.Batch0978
