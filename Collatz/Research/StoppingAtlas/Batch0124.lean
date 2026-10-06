import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0124

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 865. -/
theorem bounds_11_865 : exactInterval 11 865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_865 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 865) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_865 : oddCount 865 11 = 8 ∧ acceleratedOrbit 11 865 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_865 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 865) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_865.1, data_11_865.2]

/-- Complete interval computation for depth 11, residue 866. -/
theorem bounds_11_866 : exactInterval 11 866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_866 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 866) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_866 : oddCount 866 11 = 4 ∧ acceleratedOrbit 11 866 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_866 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 866) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_866.1, data_11_866.2]

/-- Complete interval computation for depth 11, residue 867. -/
theorem bounds_11_867 : exactInterval 11 867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_867 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 867) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_867 : oddCount 867 11 = 4 ∧ acceleratedOrbit 11 867 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_867 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 867) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_867.1, data_11_867.2]

/-- Complete interval computation for depth 11, residue 868. -/
theorem bounds_11_868 : exactInterval 11 868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_868 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 868) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_868 : oddCount 868 11 = 4 ∧ acceleratedOrbit 11 868 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_868 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 868) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_868.1, data_11_868.2]

/-- Complete interval computation for depth 11, residue 869. -/
theorem bounds_11_869 : exactInterval 11 869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_869 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 869) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_869 : oddCount 869 11 = 4 ∧ acceleratedOrbit 11 869 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_869 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 869) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_869.1, data_11_869.2]

/-- Complete interval computation for depth 11, residue 870. -/
theorem bounds_11_870 : exactInterval 11 870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_870 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 870) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_870 : oddCount 870 11 = 4 ∧ acceleratedOrbit 11 870 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_870 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 870) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_870.1, data_11_870.2]

/-- Complete interval computation for depth 11, residue 871. -/
theorem bounds_11_871 : exactInterval 11 871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_871 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 871) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_871 : oddCount 871 11 = 9 ∧ acceleratedOrbit 11 871 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_871 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 871) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_871.1, data_11_871.2]

/-- Complete interval computation for depth 11, residue 872. -/
theorem bounds_11_872 : exactInterval 11 872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_872 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 872) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_872 : oddCount 872 11 = 5 ∧ acceleratedOrbit 11 872 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_872 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 872) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_872.1, data_11_872.2]

/-- Complete interval computation for depth 11, residue 873. -/
theorem bounds_11_873 : exactInterval 11 873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_873 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 873) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_873 : oddCount 873 11 = 7 ∧ acceleratedOrbit 11 873 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_873 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 873) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_873.1, data_11_873.2]

/-- Complete interval computation for depth 11, residue 874. -/
theorem bounds_11_874 : exactInterval 11 874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_874 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 874) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_874 : oddCount 874 11 = 5 ∧ acceleratedOrbit 11 874 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_874 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 874) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_874.1, data_11_874.2]

/-- Complete interval computation for depth 11, residue 875. -/
theorem bounds_11_875 : exactInterval 11 875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_875 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 875) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_875 : oddCount 875 11 = 5 ∧ acceleratedOrbit 11 875 = 104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_875 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 875) = 3 ^ 5 * m + 104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_875.1, data_11_875.2]

/-- Complete interval computation for depth 11, residue 876. -/
theorem bounds_11_876 : exactInterval 11 876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_876 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 876) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_876 : oddCount 876 11 = 6 ∧ acceleratedOrbit 11 876 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_876 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 876) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_876.1, data_11_876.2]

/-- Complete interval computation for depth 11, residue 877. -/
theorem bounds_11_877 : exactInterval 11 877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_877 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 877) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_877 : oddCount 877 11 = 6 ∧ acceleratedOrbit 11 877 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_877 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 877) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_877.1, data_11_877.2]

/-- Complete interval computation for depth 11, residue 878. -/
theorem bounds_11_878 : exactInterval 11 878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_878 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 878) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_878 : oddCount 878 11 = 6 ∧ acceleratedOrbit 11 878 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_878 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 878) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_878.1, data_11_878.2]

/-- Complete interval computation for depth 11, residue 879. -/
theorem bounds_11_879 : exactInterval 11 879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_879 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 879) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_879 : oddCount 879 11 = 7 ∧ acceleratedOrbit 11 879 = 940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_879 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 879) = 3 ^ 7 * m + 940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_879.1, data_11_879.2]

end Collatz.Research.StoppingAtlas.Batch0124
