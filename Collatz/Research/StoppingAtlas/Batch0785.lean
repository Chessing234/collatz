import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0785

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4874. -/
theorem bounds_13_4874 : exactInterval 13 4874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4874 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4874) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4874 : oddCount 4874 13 = 5 ∧ acceleratedOrbit 13 4874 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4874 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4874) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4874.1, data_13_4874.2]

/-- Complete interval computation for depth 13, residue 4875. -/
theorem bounds_13_4875 : exactInterval 13 4875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4875 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4875) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4875 : oddCount 4875 13 = 8 ∧ acceleratedOrbit 13 4875 = 3908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4875 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4875) = 3 ^ 8 * m + 3908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4875.1, data_13_4875.2]

/-- Complete interval computation for depth 13, residue 4876. -/
theorem bounds_13_4876 : exactInterval 13 4876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4876 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4876) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4876 : oddCount 4876 13 = 5 ∧ acceleratedOrbit 13 4876 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4876 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4876) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4876.1, data_13_4876.2]

/-- Complete interval computation for depth 13, residue 4877. -/
theorem bounds_13_4877 : exactInterval 13 4877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4877 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4877) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4877 : oddCount 4877 13 = 5 ∧ acceleratedOrbit 13 4877 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4877 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4877) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4877.1, data_13_4877.2]

/-- Complete interval computation for depth 13, residue 4878. -/
theorem bounds_13_4878 : exactInterval 13 4878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4878 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4878) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4878 : oddCount 4878 13 = 5 ∧ acceleratedOrbit 13 4878 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4878 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4878) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4878.1, data_13_4878.2]

/-- Complete interval computation for depth 13, residue 4879. -/
theorem bounds_13_4879 : exactInterval 13 4879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4879 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4879) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4879 : oddCount 4879 13 = 5 ∧ acceleratedOrbit 13 4879 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4879 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4879) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4879.1, data_13_4879.2]

/-- Complete interval computation for depth 13, residue 4880. -/
theorem bounds_13_4880 : exactInterval 13 4880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4880 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4880) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4880 : oddCount 4880 13 = 4 ∧ acceleratedOrbit 13 4880 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4880 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4880) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4880.1, data_13_4880.2]

/-- Complete interval computation for depth 13, residue 4881. -/
theorem bounds_13_4881 : exactInterval 13 4881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4881 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4881) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4881 : oddCount 4881 13 = 5 ∧ acceleratedOrbit 13 4881 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4881 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4881) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4881.1, data_13_4881.2]

/-- Complete interval computation for depth 13, residue 4882. -/
theorem bounds_13_4882 : exactInterval 13 4882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4882 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4882) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4882 : oddCount 4882 13 = 8 ∧ acceleratedOrbit 13 4882 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4882 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4882) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4882.1, data_13_4882.2]

/-- Complete interval computation for depth 13, residue 4883. -/
theorem bounds_13_4883 : exactInterval 13 4883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4883 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4883) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4883 : oddCount 4883 13 = 8 ∧ acceleratedOrbit 13 4883 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4883 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4883) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4883.1, data_13_4883.2]

/-- Complete interval computation for depth 13, residue 4884. -/
theorem bounds_13_4884 : exactInterval 13 4884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4884 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4884) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4884 : oddCount 4884 13 = 4 ∧ acceleratedOrbit 13 4884 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4884 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4884) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4884.1, data_13_4884.2]

/-- Complete interval computation for depth 13, residue 4885. -/
theorem bounds_13_4885 : exactInterval 13 4885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4885 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4885) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4885 : oddCount 4885 13 = 4 ∧ acceleratedOrbit 13 4885 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4885 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4885) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4885.1, data_13_4885.2]

/-- Complete interval computation for depth 13, residue 4886. -/
theorem bounds_13_4886 : exactInterval 13 4886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4886 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4886) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4886 : oddCount 4886 13 = 7 ∧ acceleratedOrbit 13 4886 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4886 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4886) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4886.1, data_13_4886.2]

/-- Complete interval computation for depth 13, residue 4887. -/
theorem bounds_13_4887 : exactInterval 13 4887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4887 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4887) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4887 : oddCount 4887 13 = 7 ∧ acceleratedOrbit 13 4887 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4887 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4887) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4887.1, data_13_4887.2]

/-- Complete interval computation for depth 13, residue 4888. -/
theorem bounds_13_4888 : exactInterval 13 4888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4888 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4888) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4888 : oddCount 4888 13 = 4 ∧ acceleratedOrbit 13 4888 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4888 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4888) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4888.1, data_13_4888.2]

end Collatz.Research.StoppingAtlas.Batch0785
