import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0386

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2841. -/
theorem bounds_12_2841 : exactInterval 12 2841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2841 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2841) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2841 : oddCount 2841 12 = 8 ∧ acceleratedOrbit 12 2841 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2841 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2841) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2841.1, data_12_2841.2]

/-- Complete interval computation for depth 12, residue 2842. -/
theorem bounds_12_2842 : exactInterval 12 2842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2842 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2842) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2842 : oddCount 2842 12 = 3 ∧ acceleratedOrbit 12 2842 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2842 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2842) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2842.1, data_12_2842.2]

/-- Complete interval computation for depth 12, residue 2843. -/
theorem bounds_12_2843 : exactInterval 12 2843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2843 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2843) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2843 : oddCount 2843 12 = 10 ∧ acceleratedOrbit 12 2843 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2843 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2843) = 3 ^ 10 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2843.1, data_12_2843.2]

/-- Complete interval computation for depth 12, residue 2844. -/
theorem bounds_12_2844 : exactInterval 12 2844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2844 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2844) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2844 : oddCount 2844 12 = 5 ∧ acceleratedOrbit 12 2844 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2844 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2844) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2844.1, data_12_2844.2]

/-- Complete interval computation for depth 12, residue 2845. -/
theorem bounds_12_2845 : exactInterval 12 2845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2845 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2845) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2845 : oddCount 2845 12 = 5 ∧ acceleratedOrbit 12 2845 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2845 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2845) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2845.1, data_12_2845.2]

/-- Complete interval computation for depth 12, residue 2846. -/
theorem bounds_12_2846 : exactInterval 12 2846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2846 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2846) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2846 : oddCount 2846 12 = 5 ∧ acceleratedOrbit 12 2846 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2846 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2846) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2846.1, data_12_2846.2]

/-- Complete interval computation for depth 12, residue 2847. -/
theorem bounds_12_2847 : exactInterval 12 2847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2847 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2847) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2847 : oddCount 2847 12 = 9 ∧ acceleratedOrbit 12 2847 = 13688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2847 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2847) = 3 ^ 9 * m + 13688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2847.1, data_12_2847.2]

/-- Complete interval computation for depth 12, residue 2848. -/
theorem bounds_12_2848 : exactInterval 12 2848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2848 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2848) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2848 : oddCount 2848 12 = 3 ∧ acceleratedOrbit 12 2848 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2848 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2848) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2848.1, data_12_2848.2]

/-- Complete interval computation for depth 12, residue 2849. -/
theorem bounds_12_2849 : exactInterval 12 2849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2849 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2849) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2849 : oddCount 2849 12 = 6 ∧ acceleratedOrbit 12 2849 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2849 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2849) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2849.1, data_12_2849.2]

/-- Complete interval computation for depth 12, residue 2850. -/
theorem bounds_12_2850 : exactInterval 12 2850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2850 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2850) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2850 : oddCount 2850 12 = 5 ∧ acceleratedOrbit 12 2850 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2850 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2850) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2850.1, data_12_2850.2]

/-- Complete interval computation for depth 12, residue 2851. -/
theorem bounds_12_2851 : exactInterval 12 2851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2851 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2851) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2851 : oddCount 2851 12 = 5 ∧ acceleratedOrbit 12 2851 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2851 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2851) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2851.1, data_12_2851.2]

/-- Complete interval computation for depth 12, residue 2852. -/
theorem bounds_12_2852 : exactInterval 12 2852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2852 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2852) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2852 : oddCount 2852 12 = 5 ∧ acceleratedOrbit 12 2852 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2852 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2852) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2852.1, data_12_2852.2]

/-- Complete interval computation for depth 12, residue 2853. -/
theorem bounds_12_2853 : exactInterval 12 2853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2853 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2853) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2853 : oddCount 2853 12 = 5 ∧ acceleratedOrbit 12 2853 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2853 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2853) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2853.1, data_12_2853.2]

/-- Complete interval computation for depth 12, residue 2854. -/
theorem bounds_12_2854 : exactInterval 12 2854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2854 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2854) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2854 : oddCount 2854 12 = 5 ∧ acceleratedOrbit 12 2854 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2854 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2854) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2854.1, data_12_2854.2]

/-- Complete interval computation for depth 12, residue 2855. -/
theorem bounds_12_2855 : exactInterval 12 2855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2855 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2855) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2855 : oddCount 2855 12 = 8 ∧ acceleratedOrbit 12 2855 = 4576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2855 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2855) = 3 ^ 8 * m + 4576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2855.1, data_12_2855.2]

end Collatz.Research.StoppingAtlas.Batch0386
