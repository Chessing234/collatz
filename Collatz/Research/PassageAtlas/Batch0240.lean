import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0240

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7831. -/
theorem bounds_15_7831 : exactInterval 15 7831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7831 : oddCount 7831 15 = 6 ∧ acceleratedOrbit 15 7831 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7831) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7831.1, data_15_7831.2]

/-- Complete interval computation for depth 15, residue 7832. -/
theorem bounds_15_7832 : exactInterval 15 7832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7832 : oddCount 7832 15 = 7 ∧ acceleratedOrbit 15 7832 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7832) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7832.1, data_15_7832.2]

/-- Complete interval computation for depth 15, residue 7833. -/
theorem bounds_15_7833 : exactInterval 15 7833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7833 : oddCount 7833 15 = 9 ∧ acceleratedOrbit 15 7833 = 4708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7833) = 3 ^ 9 * m + 4708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7833.1, data_15_7833.2]

/-- Complete interval computation for depth 15, residue 7834. -/
theorem bounds_15_7834 : exactInterval 15 7834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7834 : oddCount 7834 15 = 7 ∧ acceleratedOrbit 15 7834 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7834) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7834.1, data_15_7834.2]

/-- Complete interval computation for depth 15, residue 7835. -/
theorem bounds_15_7835 : exactInterval 15 7835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7835 : oddCount 7835 15 = 10 ∧ acceleratedOrbit 15 7835 = 14122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7835) = 3 ^ 10 * m + 14122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7835.1, data_15_7835.2]

/-- Complete interval computation for depth 15, residue 7836. -/
theorem bounds_15_7836 : exactInterval 15 7836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7836 : oddCount 7836 15 = 9 ∧ acceleratedOrbit 15 7836 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7836) = 3 ^ 9 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7836.1, data_15_7836.2]

/-- Complete interval computation for depth 15, residue 7837. -/
theorem bounds_15_7837 : exactInterval 15 7837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7837 : oddCount 7837 15 = 9 ∧ acceleratedOrbit 15 7837 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7837) = 3 ^ 9 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7837.1, data_15_7837.2]

/-- Complete interval computation for depth 15, residue 7838. -/
theorem bounds_15_7838 : exactInterval 15 7838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7838 : oddCount 7838 15 = 9 ∧ acceleratedOrbit 15 7838 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7838) = 3 ^ 9 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7838.1, data_15_7838.2]

/-- Complete interval computation for depth 15, residue 7839. -/
theorem bounds_15_7839 : exactInterval 15 7839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7839 : oddCount 7839 15 = 11 ∧ acceleratedOrbit 15 7839 = 42385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7839) = 3 ^ 11 * m + 42385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7839.1, data_15_7839.2]

/-- Complete interval computation for depth 15, residue 7840. -/
theorem bounds_15_7840 : exactInterval 15 7840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7840 : oddCount 7840 15 = 4 ∧ acceleratedOrbit 15 7840 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7840) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7840.1, data_15_7840.2]

/-- Complete interval computation for depth 15, residue 7841. -/
theorem bounds_15_7841 : exactInterval 15 7841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7841 : oddCount 7841 15 = 7 ∧ acceleratedOrbit 15 7841 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7841) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7841.1, data_15_7841.2]

/-- Complete interval computation for depth 15, residue 7842. -/
theorem bounds_15_7842 : exactInterval 15 7842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7842 : oddCount 7842 15 = 7 ∧ acceleratedOrbit 15 7842 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7842) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7842.1, data_15_7842.2]

/-- Complete interval computation for depth 15, residue 7843. -/
theorem bounds_15_7843 : exactInterval 15 7843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7843 : oddCount 7843 15 = 7 ∧ acceleratedOrbit 15 7843 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7843) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7843.1, data_15_7843.2]

/-- Complete interval computation for depth 15, residue 7844. -/
theorem bounds_15_7844 : exactInterval 15 7844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7844 : oddCount 7844 15 = 11 ∧ acceleratedOrbit 15 7844 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7844) = 3 ^ 11 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7844.1, data_15_7844.2]

/-- Complete interval computation for depth 15, residue 7845. -/
theorem bounds_15_7845 : exactInterval 15 7845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7845 : oddCount 7845 15 = 11 ∧ acceleratedOrbit 15 7845 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7845) = 3 ^ 11 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7845.1, data_15_7845.2]

/-- Complete interval computation for depth 15, residue 7846. -/
theorem bounds_15_7846 : exactInterval 15 7846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7846 : oddCount 7846 15 = 11 ∧ acceleratedOrbit 15 7846 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7846) = 3 ^ 11 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7846.1, data_15_7846.2]

/-- Complete interval computation for depth 15, residue 7847. -/
theorem bounds_15_7847 : exactInterval 15 7847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7847 : oddCount 7847 15 = 9 ∧ acceleratedOrbit 15 7847 = 4715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7847) = 3 ^ 9 * m + 4715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7847.1, data_15_7847.2]

/-- Complete interval computation for depth 15, residue 7848. -/
theorem bounds_15_7848 : exactInterval 15 7848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7848 : oddCount 7848 15 = 4 ∧ acceleratedOrbit 15 7848 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7848) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7848.1, data_15_7848.2]

/-- Complete interval computation for depth 15, residue 7849. -/
theorem bounds_15_7849 : exactInterval 15 7849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7849 : oddCount 7849 15 = 12 ∧ acceleratedOrbit 15 7849 = 127325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7849) = 3 ^ 12 * m + 127325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7849.1, data_15_7849.2]

/-- Complete interval computation for depth 15, residue 7850. -/
theorem bounds_15_7850 : exactInterval 15 7850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7850 : oddCount 7850 15 = 4 ∧ acceleratedOrbit 15 7850 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7850) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7850.1, data_15_7850.2]

/-- Complete interval computation for depth 15, residue 7851. -/
theorem bounds_15_7851 : exactInterval 15 7851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7851 : oddCount 7851 15 = 9 ∧ acceleratedOrbit 15 7851 = 4718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7851) = 3 ^ 9 * m + 4718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7851.1, data_15_7851.2]

/-- Complete interval computation for depth 15, residue 7852. -/
theorem bounds_15_7852 : exactInterval 15 7852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7852 : oddCount 7852 15 = 9 ∧ acceleratedOrbit 15 7852 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7852) = 3 ^ 9 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7852.1, data_15_7852.2]

/-- Complete interval computation for depth 15, residue 7853. -/
theorem bounds_15_7853 : exactInterval 15 7853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7853 : oddCount 7853 15 = 9 ∧ acceleratedOrbit 15 7853 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7853) = 3 ^ 9 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7853.1, data_15_7853.2]

/-- Complete interval computation for depth 15, residue 7854. -/
theorem bounds_15_7854 : exactInterval 15 7854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7854 : oddCount 7854 15 = 9 ∧ acceleratedOrbit 15 7854 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7854) = 3 ^ 9 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7854.1, data_15_7854.2]

/-- Complete interval computation for depth 15, residue 7855. -/
theorem bounds_15_7855 : exactInterval 15 7855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7855 : oddCount 7855 15 = 9 ∧ acceleratedOrbit 15 7855 = 4720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7855) = 3 ^ 9 * m + 4720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7855.1, data_15_7855.2]

/-- Complete interval computation for depth 15, residue 7856. -/
theorem bounds_15_7856 : exactInterval 15 7856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7856 : oddCount 7856 15 = 8 ∧ acceleratedOrbit 15 7856 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7856) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7856.1, data_15_7856.2]

/-- Complete interval computation for depth 15, residue 7857. -/
theorem bounds_15_7857 : exactInterval 15 7857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7857 : oddCount 7857 15 = 7 ∧ acceleratedOrbit 15 7857 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7857) = 3 ^ 7 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7857.1, data_15_7857.2]

/-- Complete interval computation for depth 15, residue 7858. -/
theorem bounds_15_7858 : exactInterval 15 7858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7858 : oddCount 7858 15 = 7 ∧ acceleratedOrbit 15 7858 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7858) = 3 ^ 7 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7858.1, data_15_7858.2]

/-- Complete interval computation for depth 15, residue 7859. -/
theorem bounds_15_7859 : exactInterval 15 7859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7859 : oddCount 7859 15 = 7 ∧ acceleratedOrbit 15 7859 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7859) = 3 ^ 7 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7859.1, data_15_7859.2]

/-- Complete interval computation for depth 15, residue 7860. -/
theorem bounds_15_7860 : exactInterval 15 7860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7860 : oddCount 7860 15 = 8 ∧ acceleratedOrbit 15 7860 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7860) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7860.1, data_15_7860.2]

/-- Complete interval computation for depth 15, residue 7861. -/
theorem bounds_15_7861 : exactInterval 15 7861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7861 : oddCount 7861 15 = 8 ∧ acceleratedOrbit 15 7861 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7861) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7861.1, data_15_7861.2]

/-- Complete interval computation for depth 15, residue 7862. -/
theorem bounds_15_7862 : exactInterval 15 7862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7862 : oddCount 7862 15 = 11 ∧ acceleratedOrbit 15 7862 = 42524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7862) = 3 ^ 11 * m + 42524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7862.1, data_15_7862.2]

/-- Complete interval computation for depth 15, residue 7863. -/
theorem bounds_15_7863 : exactInterval 15 7863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7863 : oddCount 7863 15 = 11 ∧ acceleratedOrbit 15 7863 = 42524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7863) = 3 ^ 11 * m + 42524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7863.1, data_15_7863.2]

end Collatz.Research.PassageAtlas.Batch0240
