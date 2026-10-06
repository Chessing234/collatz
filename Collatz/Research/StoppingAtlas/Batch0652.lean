import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0652

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2831. -/
theorem bounds_13_2831 : exactInterval 13 2831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2831 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2831) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2831 : oddCount 2831 13 = 4 ∧ acceleratedOrbit 13 2831 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2831 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2831) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2831.1, data_13_2831.2]

/-- Complete interval computation for depth 13, residue 2832. -/
theorem bounds_13_2832 : exactInterval 13 2832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2832 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2832) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2832 : oddCount 2832 13 = 4 ∧ acceleratedOrbit 13 2832 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2832 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2832) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2832.1, data_13_2832.2]

/-- Complete interval computation for depth 13, residue 2833. -/
theorem bounds_13_2833 : exactInterval 13 2833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2833 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2833) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2833 : oddCount 2833 13 = 6 ∧ acceleratedOrbit 13 2833 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2833 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2833) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2833.1, data_13_2833.2]

/-- Complete interval computation for depth 13, residue 2834. -/
theorem bounds_13_2834 : exactInterval 13 2834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2834 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2834) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2834 : oddCount 2834 13 = 7 ∧ acceleratedOrbit 13 2834 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2834 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2834) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2834.1, data_13_2834.2]

/-- Complete interval computation for depth 13, residue 2835. -/
theorem bounds_13_2835 : exactInterval 13 2835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2835 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2835) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2835 : oddCount 2835 13 = 7 ∧ acceleratedOrbit 13 2835 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2835 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2835) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2835.1, data_13_2835.2]

/-- Complete interval computation for depth 13, residue 2836. -/
theorem bounds_13_2836 : exactInterval 13 2836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2836 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2836) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2836 : oddCount 2836 13 = 4 ∧ acceleratedOrbit 13 2836 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2836 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2836) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2836.1, data_13_2836.2]

/-- Complete interval computation for depth 13, residue 2837. -/
theorem bounds_13_2837 : exactInterval 13 2837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2837 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2837) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2837 : oddCount 2837 13 = 4 ∧ acceleratedOrbit 13 2837 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2837 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2837) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2837.1, data_13_2837.2]

/-- Complete interval computation for depth 13, residue 2838. -/
theorem bounds_13_2838 : exactInterval 13 2838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2838 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2838) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2838 : oddCount 2838 13 = 6 ∧ acceleratedOrbit 13 2838 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2838 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2838) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2838.1, data_13_2838.2]

/-- Complete interval computation for depth 13, residue 2839. -/
theorem bounds_13_2839 : exactInterval 13 2839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2839 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2839) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2839 : oddCount 2839 13 = 6 ∧ acceleratedOrbit 13 2839 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2839 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2839) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2839.1, data_13_2839.2]

/-- Complete interval computation for depth 13, residue 2840. -/
theorem bounds_13_2840 : exactInterval 13 2840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2840 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2840) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2840 : oddCount 2840 13 = 4 ∧ acceleratedOrbit 13 2840 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2840 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2840) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2840.1, data_13_2840.2]

/-- Complete interval computation for depth 13, residue 2841. -/
theorem bounds_13_2841 : exactInterval 13 2841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2841 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2841) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2841 : oddCount 2841 13 = 8 ∧ acceleratedOrbit 13 2841 = 2278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2841 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2841) = 3 ^ 8 * m + 2278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2841.1, data_13_2841.2]

/-- Complete interval computation for depth 13, residue 2842. -/
theorem bounds_13_2842 : exactInterval 13 2842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2842 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2842) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2842 : oddCount 2842 13 = 4 ∧ acceleratedOrbit 13 2842 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2842 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2842) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2842.1, data_13_2842.2]

/-- Complete interval computation for depth 13, residue 2843. -/
theorem bounds_13_2843 : exactInterval 13 2843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2843 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2843) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2843 : oddCount 2843 13 = 10 ∧ acceleratedOrbit 13 2843 = 20503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2843 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2843) = 3 ^ 10 * m + 20503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2843.1, data_13_2843.2]

/-- Complete interval computation for depth 13, residue 2844. -/
theorem bounds_13_2844 : exactInterval 13 2844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2844 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2844) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2844 : oddCount 2844 13 = 6 ∧ acceleratedOrbit 13 2844 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2844 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2844) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2844.1, data_13_2844.2]

/-- Complete interval computation for depth 13, residue 2845. -/
theorem bounds_13_2845 : exactInterval 13 2845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2845 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2845) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2845 : oddCount 2845 13 = 6 ∧ acceleratedOrbit 13 2845 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2845 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2845) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2845.1, data_13_2845.2]

end Collatz.Research.StoppingAtlas.Batch0652
