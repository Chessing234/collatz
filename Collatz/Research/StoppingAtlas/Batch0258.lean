import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0258

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 875. -/
theorem bounds_12_875 : exactInterval 12 875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_875 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 875) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_875 : oddCount 875 12 = 5 ∧ acceleratedOrbit 12 875 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_875 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 875) = 3 ^ 5 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_875.1, data_12_875.2]

/-- Complete interval computation for depth 12, residue 876. -/
theorem bounds_12_876 : exactInterval 12 876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_876 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 876) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_876 : oddCount 876 12 = 6 ∧ acceleratedOrbit 12 876 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_876 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 876) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_876.1, data_12_876.2]

/-- Complete interval computation for depth 12, residue 877. -/
theorem bounds_12_877 : exactInterval 12 877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_877 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 877) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_877 : oddCount 877 12 = 6 ∧ acceleratedOrbit 12 877 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_877 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 877) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_877.1, data_12_877.2]

/-- Complete interval computation for depth 12, residue 878. -/
theorem bounds_12_878 : exactInterval 12 878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_878 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 878) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_878 : oddCount 878 12 = 6 ∧ acceleratedOrbit 12 878 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_878 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 878) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_878.1, data_12_878.2]

/-- Complete interval computation for depth 12, residue 879. -/
theorem bounds_12_879 : exactInterval 12 879 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_879 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 879) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_879 : oddCount 879 12 = 7 ∧ acceleratedOrbit 12 879 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_879 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 879) = 3 ^ 7 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_879.1, data_12_879.2]

/-- Complete interval computation for depth 12, residue 880. -/
theorem bounds_12_880 : exactInterval 12 880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_880 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 880) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_880 : oddCount 880 12 = 6 ∧ acceleratedOrbit 12 880 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_880 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 880) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_880.1, data_12_880.2]

/-- Complete interval computation for depth 12, residue 881. -/
theorem bounds_12_881 : exactInterval 12 881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_881 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 881) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_881 : oddCount 881 12 = 6 ∧ acceleratedOrbit 12 881 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_881 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 881) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_881.1, data_12_881.2]

/-- Complete interval computation for depth 12, residue 882. -/
theorem bounds_12_882 : exactInterval 12 882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_882 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 882) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_882 : oddCount 882 12 = 5 ∧ acceleratedOrbit 12 882 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_882 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 882) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_882.1, data_12_882.2]

/-- Complete interval computation for depth 12, residue 883. -/
theorem bounds_12_883 : exactInterval 12 883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_883 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 883) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_883 : oddCount 883 12 = 5 ∧ acceleratedOrbit 12 883 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_883 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 883) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_883.1, data_12_883.2]

/-- Complete interval computation for depth 12, residue 884. -/
theorem bounds_12_884 : exactInterval 12 884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_884 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 884) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_884 : oddCount 884 12 = 6 ∧ acceleratedOrbit 12 884 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_884 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 884) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_884.1, data_12_884.2]

/-- Complete interval computation for depth 12, residue 885. -/
theorem bounds_12_885 : exactInterval 12 885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_885 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 885) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_885 : oddCount 885 12 = 6 ∧ acceleratedOrbit 12 885 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_885 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 885) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_885.1, data_12_885.2]

/-- Complete interval computation for depth 12, residue 886. -/
theorem bounds_12_886 : exactInterval 12 886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_886 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 886) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_886 : oddCount 886 12 = 7 ∧ acceleratedOrbit 12 886 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_886 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 886) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_886.1, data_12_886.2]

/-- Complete interval computation for depth 12, residue 887. -/
theorem bounds_12_887 : exactInterval 12 887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_887 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 887) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_887 : oddCount 887 12 = 7 ∧ acceleratedOrbit 12 887 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_887 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 887) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_887.1, data_12_887.2]

/-- Complete interval computation for depth 12, residue 888. -/
theorem bounds_12_888 : exactInterval 12 888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_888 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 888) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_888 : oddCount 888 12 = 7 ∧ acceleratedOrbit 12 888 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_888 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 888) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_888.1, data_12_888.2]

/-- Complete interval computation for depth 12, residue 889. -/
theorem bounds_12_889 : exactInterval 12 889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_889 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 889) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_889 : oddCount 889 12 = 9 ∧ acceleratedOrbit 12 889 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_889 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 889) = 3 ^ 9 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_889.1, data_12_889.2]

end Collatz.Research.StoppingAtlas.Batch0258
