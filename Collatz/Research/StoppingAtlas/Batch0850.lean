import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0850

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5872. -/
theorem bounds_13_5872 : exactInterval 13 5872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5872 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5872) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5872 : oddCount 5872 13 = 6 ∧ acceleratedOrbit 13 5872 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5872 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5872) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5872.1, data_13_5872.2]

/-- Complete interval computation for depth 13, residue 5873. -/
theorem bounds_13_5873 : exactInterval 13 5873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5873 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5873) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5873 : oddCount 5873 13 = 5 ∧ acceleratedOrbit 13 5873 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5873 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5873) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5873.1, data_13_5873.2]

/-- Complete interval computation for depth 13, residue 5874. -/
theorem bounds_13_5874 : exactInterval 13 5874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5874 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5874) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5874 : oddCount 5874 13 = 8 ∧ acceleratedOrbit 13 5874 = 4708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5874 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5874) = 3 ^ 8 * m + 4708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5874.1, data_13_5874.2]

/-- Complete interval computation for depth 13, residue 5875. -/
theorem bounds_13_5875 : exactInterval 13 5875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5875 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5875) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5875 : oddCount 5875 13 = 8 ∧ acceleratedOrbit 13 5875 = 4708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5875 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5875) = 3 ^ 8 * m + 4708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5875.1, data_13_5875.2]

/-- Complete interval computation for depth 13, residue 5876. -/
theorem bounds_13_5876 : exactInterval 13 5876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5876 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5876) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5876 : oddCount 5876 13 = 6 ∧ acceleratedOrbit 13 5876 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5876 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5876) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5876.1, data_13_5876.2]

/-- Complete interval computation for depth 13, residue 5877. -/
theorem bounds_13_5877 : exactInterval 13 5877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5877 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5877) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5877 : oddCount 5877 13 = 6 ∧ acceleratedOrbit 13 5877 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5877 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5877) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5877.1, data_13_5877.2]

/-- Complete interval computation for depth 13, residue 5878. -/
theorem bounds_13_5878 : exactInterval 13 5878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5878 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5878) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5878 : oddCount 5878 13 = 8 ∧ acceleratedOrbit 13 5878 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5878 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5878) = 3 ^ 8 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5878.1, data_13_5878.2]

/-- Complete interval computation for depth 13, residue 5879. -/
theorem bounds_13_5879 : exactInterval 13 5879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5879 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5879) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5879 : oddCount 5879 13 = 8 ∧ acceleratedOrbit 13 5879 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5879 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5879) = 3 ^ 8 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5879.1, data_13_5879.2]

/-- Complete interval computation for depth 13, residue 5880. -/
theorem bounds_13_5880 : exactInterval 13 5880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5880 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5880) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5880 : oddCount 5880 13 = 6 ∧ acceleratedOrbit 13 5880 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5880 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5880) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5880.1, data_13_5880.2]

/-- Complete interval computation for depth 13, residue 5881. -/
theorem bounds_13_5881 : exactInterval 13 5881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5881 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5881) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5881 : oddCount 5881 13 = 6 ∧ acceleratedOrbit 13 5881 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5881 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5881) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5881.1, data_13_5881.2]

/-- Complete interval computation for depth 13, residue 5882. -/
theorem bounds_13_5882 : exactInterval 13 5882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5882 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5882) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5882 : oddCount 5882 13 = 6 ∧ acceleratedOrbit 13 5882 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5882 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5882) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5882.1, data_13_5882.2]

/-- Complete interval computation for depth 13, residue 5883. -/
theorem bounds_13_5883 : exactInterval 13 5883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5883 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5883) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5883 : oddCount 5883 13 = 7 ∧ acceleratedOrbit 13 5883 = 1571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5883 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5883) = 3 ^ 7 * m + 1571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5883.1, data_13_5883.2]

/-- Complete interval computation for depth 13, residue 5884. -/
theorem bounds_13_5884 : exactInterval 13 5884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5884 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5884) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5884 : oddCount 5884 13 = 10 ∧ acceleratedOrbit 13 5884 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5884 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5884) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5884.1, data_13_5884.2]

/-- Complete interval computation for depth 13, residue 5885. -/
theorem bounds_13_5885 : exactInterval 13 5885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5885 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5885) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5885 : oddCount 5885 13 = 10 ∧ acceleratedOrbit 13 5885 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5885 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5885) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5885.1, data_13_5885.2]

/-- Complete interval computation for depth 13, residue 5886. -/
theorem bounds_13_5886 : exactInterval 13 5886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5886 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5886) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5886 : oddCount 5886 13 = 10 ∧ acceleratedOrbit 13 5886 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5886 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5886) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5886.1, data_13_5886.2]

/-- Complete interval computation for depth 13, residue 5887. -/
theorem bounds_13_5887 : exactInterval 13 5887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5887 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5887) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5887 : oddCount 5887 13 = 11 ∧ acceleratedOrbit 13 5887 = 127325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5887 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5887) = 3 ^ 11 * m + 127325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5887.1, data_13_5887.2]

end Collatz.Research.StoppingAtlas.Batch0850
