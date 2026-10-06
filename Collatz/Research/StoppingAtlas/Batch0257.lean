import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0257

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 860. -/
theorem bounds_12_860 : exactInterval 12 860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_860 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 860) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_860 : oddCount 860 12 = 6 ∧ acceleratedOrbit 12 860 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_860 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 860) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_860.1, data_12_860.2]

/-- Complete interval computation for depth 12, residue 861. -/
theorem bounds_12_861 : exactInterval 12 861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_861 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 861) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_861 : oddCount 861 12 = 6 ∧ acceleratedOrbit 12 861 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_861 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 861) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_861.1, data_12_861.2]

/-- Complete interval computation for depth 12, residue 862. -/
theorem bounds_12_862 : exactInterval 12 862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_862 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 862) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_862 : oddCount 862 12 = 6 ∧ acceleratedOrbit 12 862 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_862 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 862) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_862.1, data_12_862.2]

/-- Complete interval computation for depth 12, residue 863. -/
theorem bounds_12_863 : exactInterval 12 863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_863 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 863) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_863 : oddCount 863 12 = 6 ∧ acceleratedOrbit 12 863 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_863 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 863) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_863.1, data_12_863.2]

/-- Complete interval computation for depth 12, residue 864. -/
theorem bounds_12_864 : exactInterval 12 864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_864 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 864) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_864 : oddCount 864 12 = 6 ∧ acceleratedOrbit 12 864 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_864 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 864) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_864.1, data_12_864.2]

/-- Complete interval computation for depth 12, residue 865. -/
theorem bounds_12_865 : exactInterval 12 865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_865 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 865) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_865 : oddCount 865 12 = 8 ∧ acceleratedOrbit 12 865 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_865 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 865) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_865.1, data_12_865.2]

/-- Complete interval computation for depth 12, residue 866. -/
theorem bounds_12_866 : exactInterval 12 866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_866 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 866) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_866 : oddCount 866 12 = 5 ∧ acceleratedOrbit 12 866 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_866 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 866) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_866.1, data_12_866.2]

/-- Complete interval computation for depth 12, residue 867. -/
theorem bounds_12_867 : exactInterval 12 867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_867 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 867) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_867 : oddCount 867 12 = 5 ∧ acceleratedOrbit 12 867 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_867 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 867) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_867.1, data_12_867.2]

/-- Complete interval computation for depth 12, residue 868. -/
theorem bounds_12_868 : exactInterval 12 868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_868 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 868) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_868 : oddCount 868 12 = 5 ∧ acceleratedOrbit 12 868 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_868 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 868) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_868.1, data_12_868.2]

/-- Complete interval computation for depth 12, residue 869. -/
theorem bounds_12_869 : exactInterval 12 869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_869 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 869) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_869 : oddCount 869 12 = 5 ∧ acceleratedOrbit 12 869 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_869 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 869) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_869.1, data_12_869.2]

/-- Complete interval computation for depth 12, residue 870. -/
theorem bounds_12_870 : exactInterval 12 870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_870 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 870) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_870 : oddCount 870 12 = 5 ∧ acceleratedOrbit 12 870 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_870 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 870) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_870.1, data_12_870.2]

/-- Complete interval computation for depth 12, residue 871. -/
theorem bounds_12_871 : exactInterval 12 871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_871 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 871) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_871 : oddCount 871 12 = 10 ∧ acceleratedOrbit 12 871 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_871 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 871) = 3 ^ 10 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_871.1, data_12_871.2]

/-- Complete interval computation for depth 12, residue 872. -/
theorem bounds_12_872 : exactInterval 12 872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_872 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 872) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_872 : oddCount 872 12 = 6 ∧ acceleratedOrbit 12 872 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_872 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 872) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_872.1, data_12_872.2]

/-- Complete interval computation for depth 12, residue 873. -/
theorem bounds_12_873 : exactInterval 12 873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_873 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 873) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_873 : oddCount 873 12 = 8 ∧ acceleratedOrbit 12 873 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_873 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 873) = 3 ^ 8 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_873.1, data_12_873.2]

/-- Complete interval computation for depth 12, residue 874. -/
theorem bounds_12_874 : exactInterval 12 874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_874 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 874) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_874 : oddCount 874 12 = 6 ∧ acceleratedOrbit 12 874 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_874 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 874) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_874.1, data_12_874.2]

end Collatz.Research.StoppingAtlas.Batch0257
