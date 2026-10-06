import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0087

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2818. -/
theorem bounds_15_2818 : exactInterval 15 2818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2818 : oddCount 2818 15 = 9 ∧ acceleratedOrbit 15 2818 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2818) = 3 ^ 9 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2818.1, data_15_2818.2]

/-- Complete interval computation for depth 15, residue 2819. -/
theorem bounds_15_2819 : exactInterval 15 2819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2819 : oddCount 2819 15 = 9 ∧ acceleratedOrbit 15 2819 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2819) = 3 ^ 9 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2819.1, data_15_2819.2]

/-- Complete interval computation for depth 15, residue 2820. -/
theorem bounds_15_2820 : exactInterval 15 2820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2820 : oddCount 2820 15 = 4 ∧ acceleratedOrbit 15 2820 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2820) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2820.1, data_15_2820.2]

/-- Complete interval computation for depth 15, residue 2821. -/
theorem bounds_15_2821 : exactInterval 15 2821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2821 : oddCount 2821 15 = 4 ∧ acceleratedOrbit 15 2821 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2821) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2821.1, data_15_2821.2]

/-- Complete interval computation for depth 15, residue 2822. -/
theorem bounds_15_2822 : exactInterval 15 2822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2822 : oddCount 2822 15 = 4 ∧ acceleratedOrbit 15 2822 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2822) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2822.1, data_15_2822.2]

/-- Complete interval computation for depth 15, residue 2823. -/
theorem bounds_15_2823 : exactInterval 15 2823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2823 : oddCount 2823 15 = 10 ∧ acceleratedOrbit 15 2823 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2823) = 3 ^ 10 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2823.1, data_15_2823.2]

/-- Complete interval computation for depth 15, residue 2824. -/
theorem bounds_15_2824 : exactInterval 15 2824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2824 : oddCount 2824 15 = 7 ∧ acceleratedOrbit 15 2824 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2824) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2824.1, data_15_2824.2]

/-- Complete interval computation for depth 15, residue 2825. -/
theorem bounds_15_2825 : exactInterval 15 2825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2825 : oddCount 2825 15 = 10 ∧ acceleratedOrbit 15 2825 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2825) = 3 ^ 10 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2825.1, data_15_2825.2]

/-- Complete interval computation for depth 15, residue 2826. -/
theorem bounds_15_2826 : exactInterval 15 2826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2826 : oddCount 2826 15 = 7 ∧ acceleratedOrbit 15 2826 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2826) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2826.1, data_15_2826.2]

/-- Complete interval computation for depth 15, residue 2827. -/
theorem bounds_15_2827 : exactInterval 15 2827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2827 : oddCount 2827 15 = 11 ∧ acceleratedOrbit 15 2827 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2827) = 3 ^ 11 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2827.1, data_15_2827.2]

/-- Complete interval computation for depth 15, residue 2828. -/
theorem bounds_15_2828 : exactInterval 15 2828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2828 : oddCount 2828 15 = 7 ∧ acceleratedOrbit 15 2828 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2828) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2828.1, data_15_2828.2]

/-- Complete interval computation for depth 15, residue 2829. -/
theorem bounds_15_2829 : exactInterval 15 2829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2829 : oddCount 2829 15 = 7 ∧ acceleratedOrbit 15 2829 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2829) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2829.1, data_15_2829.2]

/-- Complete interval computation for depth 15, residue 2830. -/
theorem bounds_15_2830 : exactInterval 15 2830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2830 : oddCount 2830 15 = 4 ∧ acceleratedOrbit 15 2830 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2830) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2830.1, data_15_2830.2]

/-- Complete interval computation for depth 15, residue 2831. -/
theorem bounds_15_2831 : exactInterval 15 2831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2831 : oddCount 2831 15 = 4 ∧ acceleratedOrbit 15 2831 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2831) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2831.1, data_15_2831.2]

/-- Complete interval computation for depth 15, residue 2832. -/
theorem bounds_15_2832 : exactInterval 15 2832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2832 : oddCount 2832 15 = 5 ∧ acceleratedOrbit 15 2832 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2832) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2832.1, data_15_2832.2]

/-- Complete interval computation for depth 15, residue 2833. -/
theorem bounds_15_2833 : exactInterval 15 2833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2833 : oddCount 2833 15 = 7 ∧ acceleratedOrbit 15 2833 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2833) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2833.1, data_15_2833.2]

/-- Complete interval computation for depth 15, residue 2834. -/
theorem bounds_15_2834 : exactInterval 15 2834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2834 : oddCount 2834 15 = 8 ∧ acceleratedOrbit 15 2834 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2834) = 3 ^ 8 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2834.1, data_15_2834.2]

/-- Complete interval computation for depth 15, residue 2835. -/
theorem bounds_15_2835 : exactInterval 15 2835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2835 : oddCount 2835 15 = 8 ∧ acceleratedOrbit 15 2835 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2835) = 3 ^ 8 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2835.1, data_15_2835.2]

/-- Complete interval computation for depth 15, residue 2836. -/
theorem bounds_15_2836 : exactInterval 15 2836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2836 : oddCount 2836 15 = 5 ∧ acceleratedOrbit 15 2836 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2836) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2836.1, data_15_2836.2]

/-- Complete interval computation for depth 15, residue 2837. -/
theorem bounds_15_2837 : exactInterval 15 2837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2837 : oddCount 2837 15 = 5 ∧ acceleratedOrbit 15 2837 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2837) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2837.1, data_15_2837.2]

/-- Complete interval computation for depth 15, residue 2838. -/
theorem bounds_15_2838 : exactInterval 15 2838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2838 : oddCount 2838 15 = 7 ∧ acceleratedOrbit 15 2838 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2838) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2838.1, data_15_2838.2]

/-- Complete interval computation for depth 15, residue 2839. -/
theorem bounds_15_2839 : exactInterval 15 2839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2839 : oddCount 2839 15 = 7 ∧ acceleratedOrbit 15 2839 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2839) = 3 ^ 7 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2839.1, data_15_2839.2]

/-- Complete interval computation for depth 15, residue 2840. -/
theorem bounds_15_2840 : exactInterval 15 2840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2840 : oddCount 2840 15 = 5 ∧ acceleratedOrbit 15 2840 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2840) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2840.1, data_15_2840.2]

/-- Complete interval computation for depth 15, residue 2841. -/
theorem bounds_15_2841 : exactInterval 15 2841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2841 : oddCount 2841 15 = 9 ∧ acceleratedOrbit 15 2841 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2841) = 3 ^ 9 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2841.1, data_15_2841.2]

/-- Complete interval computation for depth 15, residue 2842. -/
theorem bounds_15_2842 : exactInterval 15 2842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2842 : oddCount 2842 15 = 5 ∧ acceleratedOrbit 15 2842 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2842) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2842.1, data_15_2842.2]

/-- Complete interval computation for depth 15, residue 2843. -/
theorem bounds_15_2843 : exactInterval 15 2843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2843 : oddCount 2843 15 = 12 ∧ acceleratedOrbit 15 2843 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2843) = 3 ^ 12 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2843.1, data_15_2843.2]

/-- Complete interval computation for depth 15, residue 2844. -/
theorem bounds_15_2844 : exactInterval 15 2844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2844 : oddCount 2844 15 = 7 ∧ acceleratedOrbit 15 2844 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2844) = 3 ^ 7 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2844.1, data_15_2844.2]

/-- Complete interval computation for depth 15, residue 2845. -/
theorem bounds_15_2845 : exactInterval 15 2845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2845 : oddCount 2845 15 = 7 ∧ acceleratedOrbit 15 2845 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2845) = 3 ^ 7 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2845.1, data_15_2845.2]

/-- Complete interval computation for depth 15, residue 2846. -/
theorem bounds_15_2846 : exactInterval 15 2846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2846 : oddCount 2846 15 = 7 ∧ acceleratedOrbit 15 2846 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2846) = 3 ^ 7 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2846.1, data_15_2846.2]

/-- Complete interval computation for depth 15, residue 2847. -/
theorem bounds_15_2847 : exactInterval 15 2847 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2847) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2847 : oddCount 2847 15 = 9 ∧ acceleratedOrbit 15 2847 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2847) = 3 ^ 9 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2847.1, data_15_2847.2]

/-- Complete interval computation for depth 15, residue 2848. -/
theorem bounds_15_2848 : exactInterval 15 2848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2848 : oddCount 2848 15 = 5 ∧ acceleratedOrbit 15 2848 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2848) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2848.1, data_15_2848.2]

/-- Complete interval computation for depth 15, residue 2849. -/
theorem bounds_15_2849 : exactInterval 15 2849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2849 : oddCount 2849 15 = 7 ∧ acceleratedOrbit 15 2849 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2849) = 3 ^ 7 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2849.1, data_15_2849.2]

end Collatz.Research.PassageAtlas.Batch0087
