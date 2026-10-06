import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0653

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2846. -/
theorem bounds_13_2846 : exactInterval 13 2846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2846 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2846) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2846 : oddCount 2846 13 = 6 ∧ acceleratedOrbit 13 2846 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2846 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2846) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2846.1, data_13_2846.2]

/-- Complete interval computation for depth 13, residue 2847. -/
theorem bounds_13_2847 : exactInterval 13 2847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2847 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2847) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2847 : oddCount 2847 13 = 9 ∧ acceleratedOrbit 13 2847 = 6844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2847 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2847) = 3 ^ 9 * m + 6844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2847.1, data_13_2847.2]

/-- Complete interval computation for depth 13, residue 2848. -/
theorem bounds_13_2848 : exactInterval 13 2848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2848 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2848) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2848 : oddCount 2848 13 = 4 ∧ acceleratedOrbit 13 2848 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2848 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2848) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2848.1, data_13_2848.2]

/-- Complete interval computation for depth 13, residue 2849. -/
theorem bounds_13_2849 : exactInterval 13 2849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2849 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2849) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2849 : oddCount 2849 13 = 6 ∧ acceleratedOrbit 13 2849 = 254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2849 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2849) = 3 ^ 6 * m + 254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2849.1, data_13_2849.2]

/-- Complete interval computation for depth 13, residue 2850. -/
theorem bounds_13_2850 : exactInterval 13 2850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2850 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2850) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2850 : oddCount 2850 13 = 5 ∧ acceleratedOrbit 13 2850 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2850 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2850) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2850.1, data_13_2850.2]

/-- Complete interval computation for depth 13, residue 2851. -/
theorem bounds_13_2851 : exactInterval 13 2851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2851 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2851) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2851 : oddCount 2851 13 = 5 ∧ acceleratedOrbit 13 2851 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2851 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2851) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2851.1, data_13_2851.2]

/-- Complete interval computation for depth 13, residue 2852. -/
theorem bounds_13_2852 : exactInterval 13 2852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2852 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2852) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2852 : oddCount 2852 13 = 5 ∧ acceleratedOrbit 13 2852 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2852 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2852) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2852.1, data_13_2852.2]

/-- Complete interval computation for depth 13, residue 2853. -/
theorem bounds_13_2853 : exactInterval 13 2853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2853 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2853) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2853 : oddCount 2853 13 = 5 ∧ acceleratedOrbit 13 2853 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2853 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2853) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2853.1, data_13_2853.2]

/-- Complete interval computation for depth 13, residue 2854. -/
theorem bounds_13_2854 : exactInterval 13 2854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2854 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2854) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2854 : oddCount 2854 13 = 5 ∧ acceleratedOrbit 13 2854 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2854 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2854) = 3 ^ 5 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2854.1, data_13_2854.2]

/-- Complete interval computation for depth 13, residue 2855. -/
theorem bounds_13_2855 : exactInterval 13 2855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2855 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2855) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2855 : oddCount 2855 13 = 8 ∧ acceleratedOrbit 13 2855 = 2288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2855 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2855) = 3 ^ 8 * m + 2288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2855.1, data_13_2855.2]

/-- Complete interval computation for depth 13, residue 2856. -/
theorem bounds_13_2856 : exactInterval 13 2856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2856 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2856) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2856 : oddCount 2856 13 = 4 ∧ acceleratedOrbit 13 2856 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2856 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2856) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2856.1, data_13_2856.2]

/-- Complete interval computation for depth 13, residue 2857. -/
theorem bounds_13_2857 : exactInterval 13 2857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2857 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2857) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2857 : oddCount 2857 13 = 8 ∧ acceleratedOrbit 13 2857 = 2290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2857 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2857) = 3 ^ 8 * m + 2290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2857.1, data_13_2857.2]

/-- Complete interval computation for depth 13, residue 2858. -/
theorem bounds_13_2858 : exactInterval 13 2858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2858 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2858) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2858 : oddCount 2858 13 = 4 ∧ acceleratedOrbit 13 2858 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2858 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2858) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2858.1, data_13_2858.2]

/-- Complete interval computation for depth 13, residue 2859. -/
theorem bounds_13_2859 : exactInterval 13 2859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2859 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2859) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2859 : oddCount 2859 13 = 8 ∧ acceleratedOrbit 13 2859 = 2294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2859 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2859) = 3 ^ 8 * m + 2294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2859.1, data_13_2859.2]

/-- Complete interval computation for depth 13, residue 2860. -/
theorem bounds_13_2860 : exactInterval 13 2860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2860 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2860) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2860 : oddCount 2860 13 = 6 ∧ acceleratedOrbit 13 2860 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2860 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2860) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2860.1, data_13_2860.2]

/-- Complete interval computation for depth 13, residue 2861. -/
theorem bounds_13_2861 : exactInterval 13 2861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2861 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2861) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2861 : oddCount 2861 13 = 6 ∧ acceleratedOrbit 13 2861 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2861 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2861) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2861.1, data_13_2861.2]

end Collatz.Research.StoppingAtlas.Batch0653
