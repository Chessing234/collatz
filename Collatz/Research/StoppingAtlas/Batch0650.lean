import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0650

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2800. -/
theorem bounds_13_2800 : exactInterval 13 2800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2800 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2800) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2800 : oddCount 2800 13 = 6 ∧ acceleratedOrbit 13 2800 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2800 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2800) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2800.1, data_13_2800.2]

/-- Complete interval computation for depth 13, residue 2801. -/
theorem bounds_13_2801 : exactInterval 13 2801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2801 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2801) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2801 : oddCount 2801 13 = 4 ∧ acceleratedOrbit 13 2801 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2801 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2801) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2801.1, data_13_2801.2]

/-- Complete interval computation for depth 13, residue 2802. -/
theorem bounds_13_2802 : exactInterval 13 2802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2802 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2802) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2802 : oddCount 2802 13 = 9 ∧ acceleratedOrbit 13 2802 = 6743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2802 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2802) = 3 ^ 9 * m + 6743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2802.1, data_13_2802.2]

/-- Complete interval computation for depth 13, residue 2803. -/
theorem bounds_13_2803 : exactInterval 13 2803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2803 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2803) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2803 : oddCount 2803 13 = 9 ∧ acceleratedOrbit 13 2803 = 6743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2803 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2803) = 3 ^ 9 * m + 6743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2803.1, data_13_2803.2]

/-- Complete interval computation for depth 13, residue 2804. -/
theorem bounds_13_2804 : exactInterval 13 2804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2804 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2804) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2804 : oddCount 2804 13 = 6 ∧ acceleratedOrbit 13 2804 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2804 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2804) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2804.1, data_13_2804.2]

/-- Complete interval computation for depth 13, residue 2805. -/
theorem bounds_13_2805 : exactInterval 13 2805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2805 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2805) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2805 : oddCount 2805 13 = 6 ∧ acceleratedOrbit 13 2805 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2805 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2805) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2805.1, data_13_2805.2]

/-- Complete interval computation for depth 13, residue 2806. -/
theorem bounds_13_2806 : exactInterval 13 2806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2806 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2806) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2806 : oddCount 2806 13 = 6 ∧ acceleratedOrbit 13 2806 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2806 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2806) = 3 ^ 6 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2806.1, data_13_2806.2]

/-- Complete interval computation for depth 13, residue 2807. -/
theorem bounds_13_2807 : exactInterval 13 2807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2807 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2807) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2807 : oddCount 2807 13 = 6 ∧ acceleratedOrbit 13 2807 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2807 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2807) = 3 ^ 6 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2807.1, data_13_2807.2]

/-- Complete interval computation for depth 13, residue 2808. -/
theorem bounds_13_2808 : exactInterval 13 2808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2808 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2808) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2808 : oddCount 2808 13 = 6 ∧ acceleratedOrbit 13 2808 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2808 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2808) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2808.1, data_13_2808.2]

/-- Complete interval computation for depth 13, residue 2809. -/
theorem bounds_13_2809 : exactInterval 13 2809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2809 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2809) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2809 : oddCount 2809 13 = 7 ∧ acceleratedOrbit 13 2809 = 751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2809 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2809) = 3 ^ 7 * m + 751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2809.1, data_13_2809.2]

/-- Complete interval computation for depth 13, residue 2810. -/
theorem bounds_13_2810 : exactInterval 13 2810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2810 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2810) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2810 : oddCount 2810 13 = 6 ∧ acceleratedOrbit 13 2810 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2810 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2810) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2810.1, data_13_2810.2]

/-- Complete interval computation for depth 13, residue 2811. -/
theorem bounds_13_2811 : exactInterval 13 2811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2811 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2811) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2811 : oddCount 2811 13 = 10 ∧ acceleratedOrbit 13 2811 = 20276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2811 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2811) = 3 ^ 10 * m + 20276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2811.1, data_13_2811.2]

/-- Complete interval computation for depth 13, residue 2812. -/
theorem bounds_13_2812 : exactInterval 13 2812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2812 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2812) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2812 : oddCount 2812 13 = 9 ∧ acceleratedOrbit 13 2812 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2812 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2812) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2812.1, data_13_2812.2]

/-- Complete interval computation for depth 13, residue 2813. -/
theorem bounds_13_2813 : exactInterval 13 2813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2813 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2813) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2813 : oddCount 2813 13 = 9 ∧ acceleratedOrbit 13 2813 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2813 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2813) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2813.1, data_13_2813.2]

/-- Complete interval computation for depth 13, residue 2814. -/
theorem bounds_13_2814 : exactInterval 13 2814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2814 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2814) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2814 : oddCount 2814 13 = 9 ∧ acceleratedOrbit 13 2814 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2814 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2814) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2814.1, data_13_2814.2]

/-- Complete interval computation for depth 13, residue 2815. -/
theorem bounds_13_2815 : exactInterval 13 2815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2815 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2815) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2815 : oddCount 2815 13 = 9 ∧ acceleratedOrbit 13 2815 = 6766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2815 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2815) = 3 ^ 9 * m + 6766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2815.1, data_13_2815.2]

end Collatz.Research.StoppingAtlas.Batch0650
