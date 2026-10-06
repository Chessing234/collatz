import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0027

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 851. -/
theorem bounds_15_851 : exactInterval 15 851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_851 : oddCount 851 15 = 11 ∧ acceleratedOrbit 15 851 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 851) = 3 ^ 11 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_851.1, data_15_851.2]

/-- Complete interval computation for depth 15, residue 852. -/
theorem bounds_15_852 : exactInterval 15 852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_852 : oddCount 852 15 = 3 ∧ acceleratedOrbit 15 852 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 852) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_852.1, data_15_852.2]

/-- Complete interval computation for depth 15, residue 853. -/
theorem bounds_15_853 : exactInterval 15 853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_853 : oddCount 853 15 = 3 ∧ acceleratedOrbit 15 853 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 853) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_853.1, data_15_853.2]

/-- Complete interval computation for depth 15, residue 854. -/
theorem bounds_15_854 : exactInterval 15 854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_854 : oddCount 854 15 = 8 ∧ acceleratedOrbit 15 854 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 854) = 3 ^ 8 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_854.1, data_15_854.2]

/-- Complete interval computation for depth 15, residue 855. -/
theorem bounds_15_855 : exactInterval 15 855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_855 : oddCount 855 15 = 8 ∧ acceleratedOrbit 15 855 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 855) = 3 ^ 8 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_855.1, data_15_855.2]

/-- Complete interval computation for depth 15, residue 856. -/
theorem bounds_15_856 : exactInterval 15 856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_856 : oddCount 856 15 = 8 ∧ acceleratedOrbit 15 856 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 856) = 3 ^ 8 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_856.1, data_15_856.2]

/-- Complete interval computation for depth 15, residue 857. -/
theorem bounds_15_857 : exactInterval 15 857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_857 : oddCount 857 15 = 6 ∧ acceleratedOrbit 15 857 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 857) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_857.1, data_15_857.2]

/-- Complete interval computation for depth 15, residue 858. -/
theorem bounds_15_858 : exactInterval 15 858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_858 : oddCount 858 15 = 8 ∧ acceleratedOrbit 15 858 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 858) = 3 ^ 8 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_858.1, data_15_858.2]

/-- Complete interval computation for depth 15, residue 859. -/
theorem bounds_15_859 : exactInterval 15 859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_859 : oddCount 859 15 = 10 ∧ acceleratedOrbit 15 859 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 859) = 3 ^ 10 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_859.1, data_15_859.2]

/-- Complete interval computation for depth 15, residue 860. -/
theorem bounds_15_860 : exactInterval 15 860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_860 : oddCount 860 15 = 8 ∧ acceleratedOrbit 15 860 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 860) = 3 ^ 8 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_860.1, data_15_860.2]

/-- Complete interval computation for depth 15, residue 861. -/
theorem bounds_15_861 : exactInterval 15 861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_861 : oddCount 861 15 = 8 ∧ acceleratedOrbit 15 861 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 861) = 3 ^ 8 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_861.1, data_15_861.2]

/-- Complete interval computation for depth 15, residue 862. -/
theorem bounds_15_862 : exactInterval 15 862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_862 : oddCount 862 15 = 7 ∧ acceleratedOrbit 15 862 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 862) = 3 ^ 7 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_862.1, data_15_862.2]

/-- Complete interval computation for depth 15, residue 863. -/
theorem bounds_15_863 : exactInterval 15 863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_863 : oddCount 863 15 = 7 ∧ acceleratedOrbit 15 863 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 863) = 3 ^ 7 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_863.1, data_15_863.2]

/-- Complete interval computation for depth 15, residue 864. -/
theorem bounds_15_864 : exactInterval 15 864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_864 : oddCount 864 15 = 8 ∧ acceleratedOrbit 15 864 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 864) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_864.1, data_15_864.2]

/-- Complete interval computation for depth 15, residue 865. -/
theorem bounds_15_865 : exactInterval 15 865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_865 : oddCount 865 15 = 10 ∧ acceleratedOrbit 15 865 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 865) = 3 ^ 10 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_865.1, data_15_865.2]

/-- Complete interval computation for depth 15, residue 866. -/
theorem bounds_15_866 : exactInterval 15 866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_866 : oddCount 866 15 = 6 ∧ acceleratedOrbit 15 866 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 866) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_866.1, data_15_866.2]

/-- Complete interval computation for depth 15, residue 867. -/
theorem bounds_15_867 : exactInterval 15 867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_867 : oddCount 867 15 = 6 ∧ acceleratedOrbit 15 867 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 867) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_867.1, data_15_867.2]

/-- Complete interval computation for depth 15, residue 868. -/
theorem bounds_15_868 : exactInterval 15 868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_868 : oddCount 868 15 = 6 ∧ acceleratedOrbit 15 868 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 868) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_868.1, data_15_868.2]

/-- Complete interval computation for depth 15, residue 869. -/
theorem bounds_15_869 : exactInterval 15 869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_869 : oddCount 869 15 = 6 ∧ acceleratedOrbit 15 869 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 869) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_869.1, data_15_869.2]

/-- Complete interval computation for depth 15, residue 870. -/
theorem bounds_15_870 : exactInterval 15 870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_870 : oddCount 870 15 = 6 ∧ acceleratedOrbit 15 870 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 870) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_870.1, data_15_870.2]

/-- Complete interval computation for depth 15, residue 871. -/
theorem bounds_15_871 : exactInterval 15 871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_871 : oddCount 871 15 = 13 ∧ acceleratedOrbit 15 871 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 871) = 3 ^ 13 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_871.1, data_15_871.2]

/-- Complete interval computation for depth 15, residue 872. -/
theorem bounds_15_872 : exactInterval 15 872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_872 : oddCount 872 15 = 8 ∧ acceleratedOrbit 15 872 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 872) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_872.1, data_15_872.2]

/-- Complete interval computation for depth 15, residue 873. -/
theorem bounds_15_873 : exactInterval 15 873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_873 : oddCount 873 15 = 10 ∧ acceleratedOrbit 15 873 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 873) = 3 ^ 10 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_873.1, data_15_873.2]

/-- Complete interval computation for depth 15, residue 874. -/
theorem bounds_15_874 : exactInterval 15 874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_874 : oddCount 874 15 = 8 ∧ acceleratedOrbit 15 874 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 874) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_874.1, data_15_874.2]

/-- Complete interval computation for depth 15, residue 875. -/
theorem bounds_15_875 : exactInterval 15 875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_875 : oddCount 875 15 = 6 ∧ acceleratedOrbit 15 875 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 875) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_875.1, data_15_875.2]

/-- Complete interval computation for depth 15, residue 876. -/
theorem bounds_15_876 : exactInterval 15 876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_876 : oddCount 876 15 = 7 ∧ acceleratedOrbit 15 876 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 876) = 3 ^ 7 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_876.1, data_15_876.2]

/-- Complete interval computation for depth 15, residue 877. -/
theorem bounds_15_877 : exactInterval 15 877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_877 : oddCount 877 15 = 7 ∧ acceleratedOrbit 15 877 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 877) = 3 ^ 7 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_877.1, data_15_877.2]

/-- Complete interval computation for depth 15, residue 878. -/
theorem bounds_15_878 : exactInterval 15 878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_878 : oddCount 878 15 = 7 ∧ acceleratedOrbit 15 878 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 878) = 3 ^ 7 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_878.1, data_15_878.2]

/-- Complete interval computation for depth 15, residue 879. -/
theorem bounds_15_879 : exactInterval 15 879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_879 : oddCount 879 15 = 9 ∧ acceleratedOrbit 15 879 = 530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 879) = 3 ^ 9 * m + 530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_879.1, data_15_879.2]

/-- Complete interval computation for depth 15, residue 880. -/
theorem bounds_15_880 : exactInterval 15 880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_880 : oddCount 880 15 = 8 ∧ acceleratedOrbit 15 880 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 880) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_880.1, data_15_880.2]

/-- Complete interval computation for depth 15, residue 881. -/
theorem bounds_15_881 : exactInterval 15 881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_881 : oddCount 881 15 = 8 ∧ acceleratedOrbit 15 881 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 881) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_881.1, data_15_881.2]

/-- Complete interval computation for depth 15, residue 882. -/
theorem bounds_15_882 : exactInterval 15 882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_882 : oddCount 882 15 = 6 ∧ acceleratedOrbit 15 882 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 882) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_882.1, data_15_882.2]

/-- Complete interval computation for depth 15, residue 883. -/
theorem bounds_15_883 : exactInterval 15 883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_883 : oddCount 883 15 = 6 ∧ acceleratedOrbit 15 883 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 883) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_883.1, data_15_883.2]

end Collatz.Research.PassageAtlas.Batch0027
