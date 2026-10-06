import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0384

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2810. -/
theorem bounds_12_2810 : exactInterval 12 2810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2810 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2810) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2810 : oddCount 2810 12 = 5 ∧ acceleratedOrbit 12 2810 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2810 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2810) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2810.1, data_12_2810.2]

/-- Complete interval computation for depth 12, residue 2811. -/
theorem bounds_12_2811 : exactInterval 12 2811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2811 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2811) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2811 : oddCount 2811 12 = 9 ∧ acceleratedOrbit 12 2811 = 13517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2811 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2811) = 3 ^ 9 * m + 13517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2811.1, data_12_2811.2]

/-- Complete interval computation for depth 12, residue 2812. -/
theorem bounds_12_2812 : exactInterval 12 2812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2812 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2812) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2812 : oddCount 2812 12 = 8 ∧ acceleratedOrbit 12 2812 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2812 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2812) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2812.1, data_12_2812.2]

/-- Complete interval computation for depth 12, residue 2813. -/
theorem bounds_12_2813 : exactInterval 12 2813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2813 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2813) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2813 : oddCount 2813 12 = 8 ∧ acceleratedOrbit 12 2813 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2813 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2813) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2813.1, data_12_2813.2]

/-- Complete interval computation for depth 12, residue 2814. -/
theorem bounds_12_2814 : exactInterval 12 2814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2814 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2814) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2814 : oddCount 2814 12 = 8 ∧ acceleratedOrbit 12 2814 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2814 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2814) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2814.1, data_12_2814.2]

/-- Complete interval computation for depth 12, residue 2815. -/
theorem bounds_12_2815 : exactInterval 12 2815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2815 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2815) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2815 : oddCount 2815 12 = 9 ∧ acceleratedOrbit 12 2815 = 13532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2815 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2815) = 3 ^ 9 * m + 13532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2815.1, data_12_2815.2]

/-- Complete interval computation for depth 12, residue 2816. -/
theorem bounds_12_2816 : exactInterval 12 2816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2816 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2816) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2816 : oddCount 2816 12 = 3 ∧ acceleratedOrbit 12 2816 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2816 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2816) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2816.1, data_12_2816.2]

/-- Complete interval computation for depth 12, residue 2817. -/
theorem bounds_12_2817 : exactInterval 12 2817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2817 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2817) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2817 : oddCount 2817 12 = 6 ∧ acceleratedOrbit 12 2817 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2817 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2817) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2817.1, data_12_2817.2]

/-- Complete interval computation for depth 12, residue 2818. -/
theorem bounds_12_2818 : exactInterval 12 2818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2818 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2818) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2818 : oddCount 2818 12 = 6 ∧ acceleratedOrbit 12 2818 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2818 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2818) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2818.1, data_12_2818.2]

/-- Complete interval computation for depth 12, residue 2819. -/
theorem bounds_12_2819 : exactInterval 12 2819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2819 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2819) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2819 : oddCount 2819 12 = 6 ∧ acceleratedOrbit 12 2819 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2819 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2819) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2819.1, data_12_2819.2]

/-- Complete interval computation for depth 12, residue 2820. -/
theorem bounds_12_2820 : exactInterval 12 2820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2820 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2820) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2820 : oddCount 2820 12 = 4 ∧ acceleratedOrbit 12 2820 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2820 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2820) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2820.1, data_12_2820.2]

/-- Complete interval computation for depth 12, residue 2821. -/
theorem bounds_12_2821 : exactInterval 12 2821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2821 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2821) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2821 : oddCount 2821 12 = 4 ∧ acceleratedOrbit 12 2821 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2821 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2821) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2821.1, data_12_2821.2]

/-- Complete interval computation for depth 12, residue 2822. -/
theorem bounds_12_2822 : exactInterval 12 2822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2822 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2822) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2822 : oddCount 2822 12 = 4 ∧ acceleratedOrbit 12 2822 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2822 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2822) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2822.1, data_12_2822.2]

/-- Complete interval computation for depth 12, residue 2823. -/
theorem bounds_12_2823 : exactInterval 12 2823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2823 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2823) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2823 : oddCount 2823 12 = 8 ∧ acceleratedOrbit 12 2823 = 4526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2823 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2823) = 3 ^ 8 * m + 4526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2823.1, data_12_2823.2]

/-- Complete interval computation for depth 12, residue 2824. -/
theorem bounds_12_2824 : exactInterval 12 2824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2824 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2824) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2824 : oddCount 2824 12 = 6 ∧ acceleratedOrbit 12 2824 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2824 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2824) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2824.1, data_12_2824.2]

/-- Complete interval computation for depth 12, residue 2825. -/
theorem bounds_12_2825 : exactInterval 12 2825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2825 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2825) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2825 : oddCount 2825 12 = 8 ∧ acceleratedOrbit 12 2825 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2825 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2825) = 3 ^ 8 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2825.1, data_12_2825.2]

end Collatz.Research.StoppingAtlas.Batch0384
