import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0058

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 875. -/
theorem bounds_10_875 : exactInterval 10 875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_875 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 875) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_875 : oddCount 875 10 = 5 ∧ acceleratedOrbit 10 875 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_875 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 875) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_875.1, data_10_875.2]

/-- Complete interval computation for depth 10, residue 876. -/
theorem bounds_10_876 : exactInterval 10 876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_876 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 876) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_876 : oddCount 876 10 = 5 ∧ acceleratedOrbit 10 876 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_876 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 876) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_876.1, data_10_876.2]

/-- Complete interval computation for depth 10, residue 877. -/
theorem bounds_10_877 : exactInterval 10 877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_877 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 877) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_877 : oddCount 877 10 = 5 ∧ acceleratedOrbit 10 877 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_877 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 877) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_877.1, data_10_877.2]

/-- Complete interval computation for depth 10, residue 878. -/
theorem bounds_10_878 : exactInterval 10 878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_878 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 878) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_878 : oddCount 878 10 = 5 ∧ acceleratedOrbit 10 878 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_878 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 878) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_878.1, data_10_878.2]

/-- Complete interval computation for depth 10, residue 879. -/
theorem bounds_10_879 : exactInterval 10 879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_879 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 879) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_879 : oddCount 879 10 = 7 ∧ acceleratedOrbit 10 879 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_879 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 879) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_879.1, data_10_879.2]

/-- Complete interval computation for depth 10, residue 880. -/
theorem bounds_10_880 : exactInterval 10 880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_880 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 880) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_880 : oddCount 880 10 = 4 ∧ acceleratedOrbit 10 880 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_880 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 880) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_880.1, data_10_880.2]

/-- Complete interval computation for depth 10, residue 881. -/
theorem bounds_10_881 : exactInterval 10 881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_881 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 881) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_881 : oddCount 881 10 = 4 ∧ acceleratedOrbit 10 881 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_881 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 881) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_881.1, data_10_881.2]

/-- Complete interval computation for depth 10, residue 882. -/
theorem bounds_10_882 : exactInterval 10 882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_882 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 882) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_882 : oddCount 882 10 = 4 ∧ acceleratedOrbit 10 882 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_882 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 882) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_882.1, data_10_882.2]

/-- Complete interval computation for depth 10, residue 883. -/
theorem bounds_10_883 : exactInterval 10 883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_883 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 883) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_883 : oddCount 883 10 = 4 ∧ acceleratedOrbit 10 883 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_883 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 883) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_883.1, data_10_883.2]

/-- Complete interval computation for depth 10, residue 884. -/
theorem bounds_10_884 : exactInterval 10 884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_884 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 884) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_884 : oddCount 884 10 = 4 ∧ acceleratedOrbit 10 884 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_884 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 884) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_884.1, data_10_884.2]

/-- Complete interval computation for depth 10, residue 885. -/
theorem bounds_10_885 : exactInterval 10 885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_885 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 885) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_885 : oddCount 885 10 = 4 ∧ acceleratedOrbit 10 885 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_885 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 885) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_885.1, data_10_885.2]

/-- Complete interval computation for depth 10, residue 886. -/
theorem bounds_10_886 : exactInterval 10 886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_886 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 886) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_886 : oddCount 886 10 = 5 ∧ acceleratedOrbit 10 886 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_886 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 886) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_886.1, data_10_886.2]

/-- Complete interval computation for depth 10, residue 887. -/
theorem bounds_10_887 : exactInterval 10 887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_887 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 887) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_887 : oddCount 887 10 = 5 ∧ acceleratedOrbit 10 887 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_887 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 887) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_887.1, data_10_887.2]

/-- Complete interval computation for depth 10, residue 888. -/
theorem bounds_10_888 : exactInterval 10 888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_888 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 888) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_888 : oddCount 888 10 = 6 ∧ acceleratedOrbit 10 888 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_888 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 888) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_888.1, data_10_888.2]

/-- Complete interval computation for depth 10, residue 889. -/
theorem bounds_10_889 : exactInterval 10 889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_889 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 889) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_889 : oddCount 889 10 = 7 ∧ acceleratedOrbit 10 889 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_889 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 889) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_889.1, data_10_889.2]

end Collatz.Research.StoppingAtlas.Batch0058
