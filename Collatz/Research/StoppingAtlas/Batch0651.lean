import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0651

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2816. -/
theorem bounds_13_2816 : exactInterval 13 2816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2816 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2816) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2816 : oddCount 2816 13 = 3 ∧ acceleratedOrbit 13 2816 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2816 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2816) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2816.1, data_13_2816.2]

/-- Complete interval computation for depth 13, residue 2817. -/
theorem bounds_13_2817 : exactInterval 13 2817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2817 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2817) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2817 : oddCount 2817 13 = 7 ∧ acceleratedOrbit 13 2817 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2817 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2817) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2817.1, data_13_2817.2]

/-- Complete interval computation for depth 13, residue 2818. -/
theorem bounds_13_2818 : exactInterval 13 2818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2818 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2818) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2818 : oddCount 2818 13 = 7 ∧ acceleratedOrbit 13 2818 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2818 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2818) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2818.1, data_13_2818.2]

/-- Complete interval computation for depth 13, residue 2819. -/
theorem bounds_13_2819 : exactInterval 13 2819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2819 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2819) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2819 : oddCount 2819 13 = 7 ∧ acceleratedOrbit 13 2819 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2819 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2819) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2819.1, data_13_2819.2]

/-- Complete interval computation for depth 13, residue 2820. -/
theorem bounds_13_2820 : exactInterval 13 2820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2820 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2820) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2820 : oddCount 2820 13 = 4 ∧ acceleratedOrbit 13 2820 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2820 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2820) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2820.1, data_13_2820.2]

/-- Complete interval computation for depth 13, residue 2821. -/
theorem bounds_13_2821 : exactInterval 13 2821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2821 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2821) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2821 : oddCount 2821 13 = 4 ∧ acceleratedOrbit 13 2821 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2821 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2821) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2821.1, data_13_2821.2]

/-- Complete interval computation for depth 13, residue 2822. -/
theorem bounds_13_2822 : exactInterval 13 2822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2822 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2822) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2822 : oddCount 2822 13 = 4 ∧ acceleratedOrbit 13 2822 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2822 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2822) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2822.1, data_13_2822.2]

/-- Complete interval computation for depth 13, residue 2823. -/
theorem bounds_13_2823 : exactInterval 13 2823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2823 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2823) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2823 : oddCount 2823 13 = 8 ∧ acceleratedOrbit 13 2823 = 2263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2823 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2823) = 3 ^ 8 * m + 2263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2823.1, data_13_2823.2]

/-- Complete interval computation for depth 13, residue 2824. -/
theorem bounds_13_2824 : exactInterval 13 2824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2824 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2824) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2824 : oddCount 2824 13 = 6 ∧ acceleratedOrbit 13 2824 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2824 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2824) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2824.1, data_13_2824.2]

/-- Complete interval computation for depth 13, residue 2825. -/
theorem bounds_13_2825 : exactInterval 13 2825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2825 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2825) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2825 : oddCount 2825 13 = 9 ∧ acceleratedOrbit 13 2825 = 6794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2825 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2825) = 3 ^ 9 * m + 6794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2825.1, data_13_2825.2]

/-- Complete interval computation for depth 13, residue 2826. -/
theorem bounds_13_2826 : exactInterval 13 2826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2826 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2826) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2826 : oddCount 2826 13 = 6 ∧ acceleratedOrbit 13 2826 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2826 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2826) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2826.1, data_13_2826.2]

/-- Complete interval computation for depth 13, residue 2827. -/
theorem bounds_13_2827 : exactInterval 13 2827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2827 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2827) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2827 : oddCount 2827 13 = 9 ∧ acceleratedOrbit 13 2827 = 6803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2827 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2827) = 3 ^ 9 * m + 6803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2827.1, data_13_2827.2]

/-- Complete interval computation for depth 13, residue 2828. -/
theorem bounds_13_2828 : exactInterval 13 2828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2828 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2828) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2828 : oddCount 2828 13 = 6 ∧ acceleratedOrbit 13 2828 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2828 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2828) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2828.1, data_13_2828.2]

/-- Complete interval computation for depth 13, residue 2829. -/
theorem bounds_13_2829 : exactInterval 13 2829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2829 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2829) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2829 : oddCount 2829 13 = 6 ∧ acceleratedOrbit 13 2829 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2829 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2829) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2829.1, data_13_2829.2]

/-- Complete interval computation for depth 13, residue 2830. -/
theorem bounds_13_2830 : exactInterval 13 2830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2830 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2830) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2830 : oddCount 2830 13 = 4 ∧ acceleratedOrbit 13 2830 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2830 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2830) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2830.1, data_13_2830.2]

end Collatz.Research.StoppingAtlas.Batch0651
