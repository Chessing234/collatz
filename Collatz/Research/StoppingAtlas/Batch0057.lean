import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0057

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 860. -/
theorem bounds_10_860 : exactInterval 10 860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_860 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 860) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_860 : oddCount 860 10 = 5 ∧ acceleratedOrbit 10 860 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_860 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 860) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_860.1, data_10_860.2]

/-- Complete interval computation for depth 10, residue 861. -/
theorem bounds_10_861 : exactInterval 10 861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_861 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 861) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_861 : oddCount 861 10 = 5 ∧ acceleratedOrbit 10 861 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_861 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 861) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_861.1, data_10_861.2]

/-- Complete interval computation for depth 10, residue 862. -/
theorem bounds_10_862 : exactInterval 10 862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_862 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 862) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_862 : oddCount 862 10 = 5 ∧ acceleratedOrbit 10 862 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_862 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 862) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_862.1, data_10_862.2]

/-- Complete interval computation for depth 10, residue 863. -/
theorem bounds_10_863 : exactInterval 10 863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_863 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 863) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_863 : oddCount 863 10 = 5 ∧ acceleratedOrbit 10 863 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_863 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 863) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_863.1, data_10_863.2]

/-- Complete interval computation for depth 10, residue 864. -/
theorem bounds_10_864 : exactInterval 10 864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_864 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 864) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_864 : oddCount 864 10 = 4 ∧ acceleratedOrbit 10 864 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_864 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 864) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_864.1, data_10_864.2]

/-- Complete interval computation for depth 10, residue 865. -/
theorem bounds_10_865 : exactInterval 10 865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_865 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 865) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_865 : oddCount 865 10 = 7 ∧ acceleratedOrbit 10 865 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_865 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 865) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_865.1, data_10_865.2]

/-- Complete interval computation for depth 10, residue 866. -/
theorem bounds_10_866 : exactInterval 10 866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_866 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 866) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_866 : oddCount 866 10 = 3 ∧ acceleratedOrbit 10 866 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_866 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 866) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_866.1, data_10_866.2]

/-- Complete interval computation for depth 10, residue 867. -/
theorem bounds_10_867 : exactInterval 10 867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_867 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 867) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_867 : oddCount 867 10 = 3 ∧ acceleratedOrbit 10 867 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_867 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 867) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_867.1, data_10_867.2]

/-- Complete interval computation for depth 10, residue 868. -/
theorem bounds_10_868 : exactInterval 10 868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_868 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 868) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_868 : oddCount 868 10 = 3 ∧ acceleratedOrbit 10 868 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_868 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 868) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_868.1, data_10_868.2]

/-- Complete interval computation for depth 10, residue 869. -/
theorem bounds_10_869 : exactInterval 10 869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_869 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 869) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_869 : oddCount 869 10 = 3 ∧ acceleratedOrbit 10 869 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_869 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 869) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_869.1, data_10_869.2]

/-- Complete interval computation for depth 10, residue 870. -/
theorem bounds_10_870 : exactInterval 10 870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_870 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 870) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_870 : oddCount 870 10 = 3 ∧ acceleratedOrbit 10 870 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_870 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 870) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_870.1, data_10_870.2]

/-- Complete interval computation for depth 10, residue 871. -/
theorem bounds_10_871 : exactInterval 10 871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_871 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 871) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_871 : oddCount 871 10 = 9 ∧ acceleratedOrbit 10 871 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_871 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 871) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_871.1, data_10_871.2]

/-- Complete interval computation for depth 10, residue 872. -/
theorem bounds_10_872 : exactInterval 10 872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_872 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 872) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_872 : oddCount 872 10 = 4 ∧ acceleratedOrbit 10 872 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_872 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 872) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_872.1, data_10_872.2]

/-- Complete interval computation for depth 10, residue 873. -/
theorem bounds_10_873 : exactInterval 10 873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_873 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 873) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_873 : oddCount 873 10 = 6 ∧ acceleratedOrbit 10 873 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_873 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 873) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_873.1, data_10_873.2]

/-- Complete interval computation for depth 10, residue 874. -/
theorem bounds_10_874 : exactInterval 10 874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_874 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 874) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_874 : oddCount 874 10 = 4 ∧ acceleratedOrbit 10 874 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_874 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 874) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_874.1, data_10_874.2]

end Collatz.Research.StoppingAtlas.Batch0057
