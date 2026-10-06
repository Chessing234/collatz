import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0180

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5865. -/
theorem bounds_15_5865 : exactInterval 15 5865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5865 : oddCount 5865 15 = 10 ∧ acceleratedOrbit 15 5865 = 10574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5865) = 3 ^ 10 * m + 10574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5865.1, data_15_5865.2]

/-- Complete interval computation for depth 15, residue 5866. -/
theorem bounds_15_5866 : exactInterval 15 5866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5866 : oddCount 5866 15 = 7 ∧ acceleratedOrbit 15 5866 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5866) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5866.1, data_15_5866.2]

/-- Complete interval computation for depth 15, residue 5867. -/
theorem bounds_15_5867 : exactInterval 15 5867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5867 : oddCount 5867 15 = 9 ∧ acceleratedOrbit 15 5867 = 3527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5867) = 3 ^ 9 * m + 3527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5867.1, data_15_5867.2]

/-- Complete interval computation for depth 15, residue 5868. -/
theorem bounds_15_5868 : exactInterval 15 5868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5868 : oddCount 5868 15 = 8 ∧ acceleratedOrbit 15 5868 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5868) = 3 ^ 8 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5868.1, data_15_5868.2]

/-- Complete interval computation for depth 15, residue 5869. -/
theorem bounds_15_5869 : exactInterval 15 5869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5869 : oddCount 5869 15 = 8 ∧ acceleratedOrbit 15 5869 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5869) = 3 ^ 8 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5869.1, data_15_5869.2]

/-- Complete interval computation for depth 15, residue 5870. -/
theorem bounds_15_5870 : exactInterval 15 5870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5870 : oddCount 5870 15 = 8 ∧ acceleratedOrbit 15 5870 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5870) = 3 ^ 8 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5870.1, data_15_5870.2]

/-- Complete interval computation for depth 15, residue 5871. -/
theorem bounds_15_5871 : exactInterval 15 5871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5871 : oddCount 5871 15 = 10 ∧ acceleratedOrbit 15 5871 = 10583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5871) = 3 ^ 10 * m + 10583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5871.1, data_15_5871.2]

/-- Complete interval computation for depth 15, residue 5872. -/
theorem bounds_15_5872 : exactInterval 15 5872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5872 : oddCount 5872 15 = 6 ∧ acceleratedOrbit 15 5872 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5872) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5872.1, data_15_5872.2]

/-- Complete interval computation for depth 15, residue 5873. -/
theorem bounds_15_5873 : exactInterval 15 5873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5873 : oddCount 5873 15 = 7 ∧ acceleratedOrbit 15 5873 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5873) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5873.1, data_15_5873.2]

/-- Complete interval computation for depth 15, residue 5874. -/
theorem bounds_15_5874 : exactInterval 15 5874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5874 : oddCount 5874 15 = 8 ∧ acceleratedOrbit 15 5874 = 1177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5874) = 3 ^ 8 * m + 1177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5874.1, data_15_5874.2]

/-- Complete interval computation for depth 15, residue 5875. -/
theorem bounds_15_5875 : exactInterval 15 5875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5875 : oddCount 5875 15 = 8 ∧ acceleratedOrbit 15 5875 = 1177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5875) = 3 ^ 8 * m + 1177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5875.1, data_15_5875.2]

/-- Complete interval computation for depth 15, residue 5876. -/
theorem bounds_15_5876 : exactInterval 15 5876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5876 : oddCount 5876 15 = 6 ∧ acceleratedOrbit 15 5876 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5876) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5876.1, data_15_5876.2]

/-- Complete interval computation for depth 15, residue 5877. -/
theorem bounds_15_5877 : exactInterval 15 5877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5877 : oddCount 5877 15 = 6 ∧ acceleratedOrbit 15 5877 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5877) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5877.1, data_15_5877.2]

/-- Complete interval computation for depth 15, residue 5878. -/
theorem bounds_15_5878 : exactInterval 15 5878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5878 : oddCount 5878 15 = 10 ∧ acceleratedOrbit 15 5878 = 10601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5878) = 3 ^ 10 * m + 10601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5878.1, data_15_5878.2]

/-- Complete interval computation for depth 15, residue 5879. -/
theorem bounds_15_5879 : exactInterval 15 5879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5879 : oddCount 5879 15 = 10 ∧ acceleratedOrbit 15 5879 = 10601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5879) = 3 ^ 10 * m + 10601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5879.1, data_15_5879.2]

/-- Complete interval computation for depth 15, residue 5880. -/
theorem bounds_15_5880 : exactInterval 15 5880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5880 : oddCount 5880 15 = 6 ∧ acceleratedOrbit 15 5880 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5880) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5880.1, data_15_5880.2]

/-- Complete interval computation for depth 15, residue 5881. -/
theorem bounds_15_5881 : exactInterval 15 5881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5881 : oddCount 5881 15 = 6 ∧ acceleratedOrbit 15 5881 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5881) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5881.1, data_15_5881.2]

/-- Complete interval computation for depth 15, residue 5882. -/
theorem bounds_15_5882 : exactInterval 15 5882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5882 : oddCount 5882 15 = 6 ∧ acceleratedOrbit 15 5882 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5882) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5882.1, data_15_5882.2]

/-- Complete interval computation for depth 15, residue 5883. -/
theorem bounds_15_5883 : exactInterval 15 5883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5883 : oddCount 5883 15 = 9 ∧ acceleratedOrbit 15 5883 = 3536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5883) = 3 ^ 9 * m + 3536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5883.1, data_15_5883.2]

/-- Complete interval computation for depth 15, residue 5884. -/
theorem bounds_15_5884 : exactInterval 15 5884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5884 : oddCount 5884 15 = 12 ∧ acceleratedOrbit 15 5884 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5884) = 3 ^ 12 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5884.1, data_15_5884.2]

/-- Complete interval computation for depth 15, residue 5885. -/
theorem bounds_15_5885 : exactInterval 15 5885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5885 : oddCount 5885 15 = 12 ∧ acceleratedOrbit 15 5885 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5885) = 3 ^ 12 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5885.1, data_15_5885.2]

/-- Complete interval computation for depth 15, residue 5886. -/
theorem bounds_15_5886 : exactInterval 15 5886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5886 : oddCount 5886 15 = 12 ∧ acceleratedOrbit 15 5886 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5886) = 3 ^ 12 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5886.1, data_15_5886.2]

/-- Complete interval computation for depth 15, residue 5887. -/
theorem bounds_15_5887 : exactInterval 15 5887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5887 : oddCount 5887 15 = 12 ∧ acceleratedOrbit 15 5887 = 95494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5887) = 3 ^ 12 * m + 95494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5887.1, data_15_5887.2]

/-- Complete interval computation for depth 15, residue 5888. -/
theorem bounds_15_5888 : exactInterval 15 5888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5888 : oddCount 5888 15 = 3 ∧ acceleratedOrbit 15 5888 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5888) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5888.1, data_15_5888.2]

/-- Complete interval computation for depth 15, residue 5889. -/
theorem bounds_15_5889 : exactInterval 15 5889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5889 : oddCount 5889 15 = 7 ∧ acceleratedOrbit 15 5889 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5889) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5889.1, data_15_5889.2]

/-- Complete interval computation for depth 15, residue 5890. -/
theorem bounds_15_5890 : exactInterval 15 5890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5890 : oddCount 5890 15 = 8 ∧ acceleratedOrbit 15 5890 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5890) = 3 ^ 8 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5890.1, data_15_5890.2]

/-- Complete interval computation for depth 15, residue 5891. -/
theorem bounds_15_5891 : exactInterval 15 5891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5891 : oddCount 5891 15 = 8 ∧ acceleratedOrbit 15 5891 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5891) = 3 ^ 8 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5891.1, data_15_5891.2]

/-- Complete interval computation for depth 15, residue 5892. -/
theorem bounds_15_5892 : exactInterval 15 5892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5892 : oddCount 5892 15 = 7 ∧ acceleratedOrbit 15 5892 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5892) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5892.1, data_15_5892.2]

/-- Complete interval computation for depth 15, residue 5893. -/
theorem bounds_15_5893 : exactInterval 15 5893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5893 : oddCount 5893 15 = 7 ∧ acceleratedOrbit 15 5893 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5893) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5893.1, data_15_5893.2]

/-- Complete interval computation for depth 15, residue 5894. -/
theorem bounds_15_5894 : exactInterval 15 5894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5894 : oddCount 5894 15 = 7 ∧ acceleratedOrbit 15 5894 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5894) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5894.1, data_15_5894.2]

/-- Complete interval computation for depth 15, residue 5895. -/
theorem bounds_15_5895 : exactInterval 15 5895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5895 : oddCount 5895 15 = 8 ∧ acceleratedOrbit 15 5895 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5895) = 3 ^ 8 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5895.1, data_15_5895.2]

/-- Complete interval computation for depth 15, residue 5896. -/
theorem bounds_15_5896 : exactInterval 15 5896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5896 : oddCount 5896 15 = 9 ∧ acceleratedOrbit 15 5896 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5896) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5896.1, data_15_5896.2]

/-- Complete interval computation for depth 15, residue 5897. -/
theorem bounds_15_5897 : exactInterval 15 5897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5897 : oddCount 5897 15 = 10 ∧ acceleratedOrbit 15 5897 = 10631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5897) = 3 ^ 10 * m + 10631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5897.1, data_15_5897.2]

end Collatz.Research.PassageAtlas.Batch0180
