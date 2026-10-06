import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0385

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2826. -/
theorem bounds_12_2826 : exactInterval 12 2826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2826 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2826) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2826 : oddCount 2826 12 = 6 ∧ acceleratedOrbit 12 2826 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2826 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2826) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2826.1, data_12_2826.2]

/-- Complete interval computation for depth 12, residue 2827. -/
theorem bounds_12_2827 : exactInterval 12 2827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2827 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2827) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2827 : oddCount 2827 12 = 8 ∧ acceleratedOrbit 12 2827 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2827 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2827) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2827.1, data_12_2827.2]

/-- Complete interval computation for depth 12, residue 2828. -/
theorem bounds_12_2828 : exactInterval 12 2828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2828 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2828) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2828 : oddCount 2828 12 = 6 ∧ acceleratedOrbit 12 2828 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2828 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2828) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2828.1, data_12_2828.2]

/-- Complete interval computation for depth 12, residue 2829. -/
theorem bounds_12_2829 : exactInterval 12 2829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2829 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2829) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2829 : oddCount 2829 12 = 6 ∧ acceleratedOrbit 12 2829 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2829 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2829) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2829.1, data_12_2829.2]

/-- Complete interval computation for depth 12, residue 2830. -/
theorem bounds_12_2830 : exactInterval 12 2830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2830 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2830) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2830 : oddCount 2830 12 = 4 ∧ acceleratedOrbit 12 2830 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2830 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2830) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2830.1, data_12_2830.2]

/-- Complete interval computation for depth 12, residue 2831. -/
theorem bounds_12_2831 : exactInterval 12 2831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2831 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2831) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2831 : oddCount 2831 12 = 4 ∧ acceleratedOrbit 12 2831 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2831 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2831) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2831.1, data_12_2831.2]

/-- Complete interval computation for depth 12, residue 2832. -/
theorem bounds_12_2832 : exactInterval 12 2832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2832 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2832) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2832 : oddCount 2832 12 = 3 ∧ acceleratedOrbit 12 2832 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2832 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2832) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2832.1, data_12_2832.2]

/-- Complete interval computation for depth 12, residue 2833. -/
theorem bounds_12_2833 : exactInterval 12 2833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2833 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2833) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2833 : oddCount 2833 12 = 6 ∧ acceleratedOrbit 12 2833 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2833 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2833) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2833.1, data_12_2833.2]

/-- Complete interval computation for depth 12, residue 2834. -/
theorem bounds_12_2834 : exactInterval 12 2834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2834 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2834) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2834 : oddCount 2834 12 = 6 ∧ acceleratedOrbit 12 2834 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2834 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2834) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2834.1, data_12_2834.2]

/-- Complete interval computation for depth 12, residue 2835. -/
theorem bounds_12_2835 : exactInterval 12 2835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2835 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2835) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2835 : oddCount 2835 12 = 6 ∧ acceleratedOrbit 12 2835 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2835 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2835) = 3 ^ 6 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2835.1, data_12_2835.2]

/-- Complete interval computation for depth 12, residue 2836. -/
theorem bounds_12_2836 : exactInterval 12 2836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2836 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2836) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2836 : oddCount 2836 12 = 3 ∧ acceleratedOrbit 12 2836 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2836 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2836) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2836.1, data_12_2836.2]

/-- Complete interval computation for depth 12, residue 2837. -/
theorem bounds_12_2837 : exactInterval 12 2837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2837 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2837) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2837 : oddCount 2837 12 = 3 ∧ acceleratedOrbit 12 2837 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2837 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2837) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2837.1, data_12_2837.2]

/-- Complete interval computation for depth 12, residue 2838. -/
theorem bounds_12_2838 : exactInterval 12 2838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2838 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2838) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2838 : oddCount 2838 12 = 6 ∧ acceleratedOrbit 12 2838 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2838 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2838) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2838.1, data_12_2838.2]

/-- Complete interval computation for depth 12, residue 2839. -/
theorem bounds_12_2839 : exactInterval 12 2839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2839 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2839) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2839 : oddCount 2839 12 = 6 ∧ acceleratedOrbit 12 2839 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2839 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2839) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2839.1, data_12_2839.2]

/-- Complete interval computation for depth 12, residue 2840. -/
theorem bounds_12_2840 : exactInterval 12 2840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2840 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2840) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2840 : oddCount 2840 12 = 3 ∧ acceleratedOrbit 12 2840 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2840 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2840) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2840.1, data_12_2840.2]

end Collatz.Research.StoppingAtlas.Batch0385
