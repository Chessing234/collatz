import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0654

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2862. -/
theorem bounds_13_2862 : exactInterval 13 2862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2862 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2862) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2862 : oddCount 2862 13 = 6 ∧ acceleratedOrbit 13 2862 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2862 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2862) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2862.1, data_13_2862.2]

/-- Complete interval computation for depth 13, residue 2863. -/
theorem bounds_13_2863 : exactInterval 13 2863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2863 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2863) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2863 : oddCount 2863 13 = 9 ∧ acceleratedOrbit 13 2863 = 6884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2863 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2863) = 3 ^ 9 * m + 6884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2863.1, data_13_2863.2]

/-- Complete interval computation for depth 13, residue 2864. -/
theorem bounds_13_2864 : exactInterval 13 2864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2864 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2864) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2864 : oddCount 2864 13 = 4 ∧ acceleratedOrbit 13 2864 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2864 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2864) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2864.1, data_13_2864.2]

/-- Complete interval computation for depth 13, residue 2865. -/
theorem bounds_13_2865 : exactInterval 13 2865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2865 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2865) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2865 : oddCount 2865 13 = 6 ∧ acceleratedOrbit 13 2865 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2865 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2865) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2865.1, data_13_2865.2]

/-- Complete interval computation for depth 13, residue 2866. -/
theorem bounds_13_2866 : exactInterval 13 2866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2866 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2866) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2866 : oddCount 2866 13 = 6 ∧ acceleratedOrbit 13 2866 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2866 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2866) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2866.1, data_13_2866.2]

/-- Complete interval computation for depth 13, residue 2867. -/
theorem bounds_13_2867 : exactInterval 13 2867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2867 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2867) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2867 : oddCount 2867 13 = 6 ∧ acceleratedOrbit 13 2867 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2867 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2867) = 3 ^ 6 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2867.1, data_13_2867.2]

/-- Complete interval computation for depth 13, residue 2868. -/
theorem bounds_13_2868 : exactInterval 13 2868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2868 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2868) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2868 : oddCount 2868 13 = 4 ∧ acceleratedOrbit 13 2868 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2868 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2868) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2868.1, data_13_2868.2]

/-- Complete interval computation for depth 13, residue 2869. -/
theorem bounds_13_2869 : exactInterval 13 2869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2869 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2869) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2869 : oddCount 2869 13 = 4 ∧ acceleratedOrbit 13 2869 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2869 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2869) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2869.1, data_13_2869.2]

/-- Complete interval computation for depth 13, residue 2870. -/
theorem bounds_13_2870 : exactInterval 13 2870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2870 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2870) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2870 : oddCount 2870 13 = 7 ∧ acceleratedOrbit 13 2870 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2870 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2870) = 3 ^ 7 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2870.1, data_13_2870.2]

/-- Complete interval computation for depth 13, residue 2871. -/
theorem bounds_13_2871 : exactInterval 13 2871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2871 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2871) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2871 : oddCount 2871 13 = 7 ∧ acceleratedOrbit 13 2871 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2871 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2871) = 3 ^ 7 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2871.1, data_13_2871.2]

/-- Complete interval computation for depth 13, residue 2872. -/
theorem bounds_13_2872 : exactInterval 13 2872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2872 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2872) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2872 : oddCount 2872 13 = 8 ∧ acceleratedOrbit 13 2872 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2872 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2872) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2872.1, data_13_2872.2]

/-- Complete interval computation for depth 13, residue 2873. -/
theorem bounds_13_2873 : exactInterval 13 2873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2873 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2873) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2873 : oddCount 2873 13 = 9 ∧ acceleratedOrbit 13 2873 = 6911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2873 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2873) = 3 ^ 9 * m + 6911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2873.1, data_13_2873.2]

/-- Complete interval computation for depth 13, residue 2874. -/
theorem bounds_13_2874 : exactInterval 13 2874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2874 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2874) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2874 : oddCount 2874 13 = 8 ∧ acceleratedOrbit 13 2874 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2874 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2874) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2874.1, data_13_2874.2]

/-- Complete interval computation for depth 13, residue 2875. -/
theorem bounds_13_2875 : exactInterval 13 2875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2875 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2875) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2875 : oddCount 2875 13 = 7 ∧ acceleratedOrbit 13 2875 = 769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2875 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2875) = 3 ^ 7 * m + 769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2875.1, data_13_2875.2]

/-- Complete interval computation for depth 13, residue 2876. -/
theorem bounds_13_2876 : exactInterval 13 2876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2876 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2876) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2876 : oddCount 2876 13 = 8 ∧ acceleratedOrbit 13 2876 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2876 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2876) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2876.1, data_13_2876.2]

end Collatz.Research.StoppingAtlas.Batch0654
