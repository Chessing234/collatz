import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0524

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 865. -/
theorem bounds_13_865 : exactInterval 13 865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_865 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 865) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_865 : oddCount 865 13 = 8 ∧ acceleratedOrbit 13 865 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_865 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 865) = 3 ^ 8 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_865.1, data_13_865.2]

/-- Complete interval computation for depth 13, residue 866. -/
theorem bounds_13_866 : exactInterval 13 866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_866 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 866) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_866 : oddCount 866 13 = 6 ∧ acceleratedOrbit 13 866 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_866 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 866) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_866.1, data_13_866.2]

/-- Complete interval computation for depth 13, residue 867. -/
theorem bounds_13_867 : exactInterval 13 867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_867 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 867) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_867 : oddCount 867 13 = 6 ∧ acceleratedOrbit 13 867 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_867 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 867) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_867.1, data_13_867.2]

/-- Complete interval computation for depth 13, residue 868. -/
theorem bounds_13_868 : exactInterval 13 868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_868 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 868) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_868 : oddCount 868 13 = 6 ∧ acceleratedOrbit 13 868 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_868 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 868) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_868.1, data_13_868.2]

/-- Complete interval computation for depth 13, residue 869. -/
theorem bounds_13_869 : exactInterval 13 869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_869 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 869) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_869 : oddCount 869 13 = 6 ∧ acceleratedOrbit 13 869 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_869 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 869) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_869.1, data_13_869.2]

/-- Complete interval computation for depth 13, residue 870. -/
theorem bounds_13_870 : exactInterval 13 870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_870 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 870) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_870 : oddCount 870 13 = 6 ∧ acceleratedOrbit 13 870 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_870 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 870) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_870.1, data_13_870.2]

/-- Complete interval computation for depth 13, residue 871. -/
theorem bounds_13_871 : exactInterval 13 871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_871 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 871) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_871 : oddCount 871 13 = 11 ∧ acceleratedOrbit 13 871 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_871 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 871) = 3 ^ 11 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_871.1, data_13_871.2]

/-- Complete interval computation for depth 13, residue 872. -/
theorem bounds_13_872 : exactInterval 13 872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_872 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 872) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_872 : oddCount 872 13 = 7 ∧ acceleratedOrbit 13 872 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_872 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 872) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_872.1, data_13_872.2]

/-- Complete interval computation for depth 13, residue 873. -/
theorem bounds_13_873 : exactInterval 13 873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_873 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 873) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_873 : oddCount 873 13 = 9 ∧ acceleratedOrbit 13 873 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_873 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 873) = 3 ^ 9 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_873.1, data_13_873.2]

/-- Complete interval computation for depth 13, residue 874. -/
theorem bounds_13_874 : exactInterval 13 874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_874 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 874) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_874 : oddCount 874 13 = 7 ∧ acceleratedOrbit 13 874 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_874 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 874) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_874.1, data_13_874.2]

/-- Complete interval computation for depth 13, residue 875. -/
theorem bounds_13_875 : exactInterval 13 875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_875 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 875) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_875 : oddCount 875 13 = 5 ∧ acceleratedOrbit 13 875 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_875 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 875) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_875.1, data_13_875.2]

/-- Complete interval computation for depth 13, residue 876. -/
theorem bounds_13_876 : exactInterval 13 876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_876 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 876) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_876 : oddCount 876 13 = 7 ∧ acceleratedOrbit 13 876 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_876 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 876) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_876.1, data_13_876.2]

/-- Complete interval computation for depth 13, residue 877. -/
theorem bounds_13_877 : exactInterval 13 877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_877 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 877) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_877 : oddCount 877 13 = 7 ∧ acceleratedOrbit 13 877 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_877 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 877) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_877.1, data_13_877.2]

/-- Complete interval computation for depth 13, residue 878. -/
theorem bounds_13_878 : exactInterval 13 878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_878 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 878) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_878 : oddCount 878 13 = 7 ∧ acceleratedOrbit 13 878 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_878 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 878) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_878.1, data_13_878.2]

/-- Complete interval computation for depth 13, residue 879. -/
theorem bounds_13_879 : exactInterval 13 879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_879 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 879) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_879 : oddCount 879 13 = 7 ∧ acceleratedOrbit 13 879 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_879 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 879) = 3 ^ 7 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_879.1, data_13_879.2]

end Collatz.Research.StoppingAtlas.Batch0524
