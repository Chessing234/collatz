import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0088

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2850. -/
theorem bounds_15_2850 : exactInterval 15 2850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2850 : oddCount 2850 15 = 6 ∧ acceleratedOrbit 15 2850 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2850) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2850.1, data_15_2850.2]

/-- Complete interval computation for depth 15, residue 2851. -/
theorem bounds_15_2851 : exactInterval 15 2851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2851 : oddCount 2851 15 = 6 ∧ acceleratedOrbit 15 2851 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2851) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2851.1, data_15_2851.2]

/-- Complete interval computation for depth 15, residue 2852. -/
theorem bounds_15_2852 : exactInterval 15 2852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2852 : oddCount 2852 15 = 6 ∧ acceleratedOrbit 15 2852 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2852) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2852.1, data_15_2852.2]

/-- Complete interval computation for depth 15, residue 2853. -/
theorem bounds_15_2853 : exactInterval 15 2853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2853 : oddCount 2853 15 = 6 ∧ acceleratedOrbit 15 2853 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2853) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2853.1, data_15_2853.2]

/-- Complete interval computation for depth 15, residue 2854. -/
theorem bounds_15_2854 : exactInterval 15 2854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2854 : oddCount 2854 15 = 6 ∧ acceleratedOrbit 15 2854 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2854) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2854.1, data_15_2854.2]

/-- Complete interval computation for depth 15, residue 2855. -/
theorem bounds_15_2855 : exactInterval 15 2855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2855 : oddCount 2855 15 = 8 ∧ acceleratedOrbit 15 2855 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2855) = 3 ^ 8 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2855.1, data_15_2855.2]

/-- Complete interval computation for depth 15, residue 2856. -/
theorem bounds_15_2856 : exactInterval 15 2856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2856 : oddCount 2856 15 = 5 ∧ acceleratedOrbit 15 2856 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2856) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2856.1, data_15_2856.2]

/-- Complete interval computation for depth 15, residue 2857. -/
theorem bounds_15_2857 : exactInterval 15 2857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2857 : oddCount 2857 15 = 9 ∧ acceleratedOrbit 15 2857 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2857) = 3 ^ 9 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2857.1, data_15_2857.2]

/-- Complete interval computation for depth 15, residue 2858. -/
theorem bounds_15_2858 : exactInterval 15 2858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2858 : oddCount 2858 15 = 5 ∧ acceleratedOrbit 15 2858 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2858) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2858.1, data_15_2858.2]

/-- Complete interval computation for depth 15, residue 2859. -/
theorem bounds_15_2859 : exactInterval 15 2859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2859 : oddCount 2859 15 = 9 ∧ acceleratedOrbit 15 2859 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2859) = 3 ^ 9 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2859.1, data_15_2859.2]

/-- Complete interval computation for depth 15, residue 2860. -/
theorem bounds_15_2860 : exactInterval 15 2860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2860 : oddCount 2860 15 = 6 ∧ acceleratedOrbit 15 2860 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2860) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2860.1, data_15_2860.2]

/-- Complete interval computation for depth 15, residue 2861. -/
theorem bounds_15_2861 : exactInterval 15 2861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2861 : oddCount 2861 15 = 6 ∧ acceleratedOrbit 15 2861 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2861) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2861.1, data_15_2861.2]

/-- Complete interval computation for depth 15, residue 2862. -/
theorem bounds_15_2862 : exactInterval 15 2862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2862 : oddCount 2862 15 = 6 ∧ acceleratedOrbit 15 2862 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2862) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2862.1, data_15_2862.2]

/-- Complete interval computation for depth 15, residue 2863. -/
theorem bounds_15_2863 : exactInterval 15 2863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2863 : oddCount 2863 15 = 9 ∧ acceleratedOrbit 15 2863 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2863) = 3 ^ 9 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2863.1, data_15_2863.2]

/-- Complete interval computation for depth 15, residue 2864. -/
theorem bounds_15_2864 : exactInterval 15 2864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2864 : oddCount 2864 15 = 5 ∧ acceleratedOrbit 15 2864 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2864) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2864.1, data_15_2864.2]

/-- Complete interval computation for depth 15, residue 2865. -/
theorem bounds_15_2865 : exactInterval 15 2865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2865 : oddCount 2865 15 = 6 ∧ acceleratedOrbit 15 2865 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2865) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2865.1, data_15_2865.2]

/-- Complete interval computation for depth 15, residue 2866. -/
theorem bounds_15_2866 : exactInterval 15 2866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2866 : oddCount 2866 15 = 6 ∧ acceleratedOrbit 15 2866 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2866) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2866.1, data_15_2866.2]

/-- Complete interval computation for depth 15, residue 2867. -/
theorem bounds_15_2867 : exactInterval 15 2867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2867 : oddCount 2867 15 = 6 ∧ acceleratedOrbit 15 2867 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2867) = 3 ^ 6 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2867.1, data_15_2867.2]

/-- Complete interval computation for depth 15, residue 2868. -/
theorem bounds_15_2868 : exactInterval 15 2868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2868 : oddCount 2868 15 = 5 ∧ acceleratedOrbit 15 2868 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2868) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2868.1, data_15_2868.2]

/-- Complete interval computation for depth 15, residue 2869. -/
theorem bounds_15_2869 : exactInterval 15 2869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2869 : oddCount 2869 15 = 5 ∧ acceleratedOrbit 15 2869 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2869) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2869.1, data_15_2869.2]

/-- Complete interval computation for depth 15, residue 2870. -/
theorem bounds_15_2870 : exactInterval 15 2870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2870 : oddCount 2870 15 = 9 ∧ acceleratedOrbit 15 2870 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2870) = 3 ^ 9 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2870.1, data_15_2870.2]

/-- Complete interval computation for depth 15, residue 2871. -/
theorem bounds_15_2871 : exactInterval 15 2871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2871 : oddCount 2871 15 = 9 ∧ acceleratedOrbit 15 2871 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2871) = 3 ^ 9 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2871.1, data_15_2871.2]

/-- Complete interval computation for depth 15, residue 2872. -/
theorem bounds_15_2872 : exactInterval 15 2872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2872 : oddCount 2872 15 = 8 ∧ acceleratedOrbit 15 2872 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2872) = 3 ^ 8 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2872.1, data_15_2872.2]

/-- Complete interval computation for depth 15, residue 2873. -/
theorem bounds_15_2873 : exactInterval 15 2873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2873 : oddCount 2873 15 = 11 ∧ acceleratedOrbit 15 2873 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2873) = 3 ^ 11 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2873.1, data_15_2873.2]

/-- Complete interval computation for depth 15, residue 2874. -/
theorem bounds_15_2874 : exactInterval 15 2874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2874 : oddCount 2874 15 = 8 ∧ acceleratedOrbit 15 2874 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2874) = 3 ^ 8 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2874.1, data_15_2874.2]

/-- Complete interval computation for depth 15, residue 2875. -/
theorem bounds_15_2875 : exactInterval 15 2875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2875 : oddCount 2875 15 = 8 ∧ acceleratedOrbit 15 2875 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2875) = 3 ^ 8 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2875.1, data_15_2875.2]

/-- Complete interval computation for depth 15, residue 2876. -/
theorem bounds_15_2876 : exactInterval 15 2876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2876 : oddCount 2876 15 = 8 ∧ acceleratedOrbit 15 2876 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2876) = 3 ^ 8 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2876.1, data_15_2876.2]

/-- Complete interval computation for depth 15, residue 2877. -/
theorem bounds_15_2877 : exactInterval 15 2877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2877 : oddCount 2877 15 = 8 ∧ acceleratedOrbit 15 2877 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2877) = 3 ^ 8 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2877.1, data_15_2877.2]

/-- Complete interval computation for depth 15, residue 2878. -/
theorem bounds_15_2878 : exactInterval 15 2878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2878 : oddCount 2878 15 = 11 ∧ acceleratedOrbit 15 2878 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2878) = 3 ^ 11 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2878.1, data_15_2878.2]

/-- Complete interval computation for depth 15, residue 2879. -/
theorem bounds_15_2879 : exactInterval 15 2879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2879 : oddCount 2879 15 = 11 ∧ acceleratedOrbit 15 2879 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2879) = 3 ^ 11 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2879.1, data_15_2879.2]

/-- Complete interval computation for depth 15, residue 2880. -/
theorem bounds_15_2880 : exactInterval 15 2880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2880 : oddCount 2880 15 = 4 ∧ acceleratedOrbit 15 2880 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2880) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2880.1, data_15_2880.2]

/-- Complete interval computation for depth 15, residue 2881. -/
theorem bounds_15_2881 : exactInterval 15 2881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2881 : oddCount 2881 15 = 5 ∧ acceleratedOrbit 15 2881 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2881) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2881.1, data_15_2881.2]

/-- Complete interval computation for depth 15, residue 2882. -/
theorem bounds_15_2882 : exactInterval 15 2882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2882 : oddCount 2882 15 = 7 ∧ acceleratedOrbit 15 2882 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2882) = 3 ^ 7 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2882.1, data_15_2882.2]

end Collatz.Research.PassageAtlas.Batch0088
