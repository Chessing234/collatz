import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0363

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11862. -/
theorem bounds_15_11862 : exactInterval 15 11862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11862 : oddCount 11862 15 = 5 ∧ acceleratedOrbit 15 11862 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11862) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11862.1, data_15_11862.2]

/-- Complete interval computation for depth 15, residue 11863. -/
theorem bounds_15_11863 : exactInterval 15 11863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11863 : oddCount 11863 15 = 5 ∧ acceleratedOrbit 15 11863 = 88 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11863) = 3 ^ 5 * m + 88 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11863.1, data_15_11863.2]

/-- Complete interval computation for depth 15, residue 11864. -/
theorem bounds_15_11864 : exactInterval 15 11864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11864 : oddCount 11864 15 = 6 ∧ acceleratedOrbit 15 11864 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11864) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11864.1, data_15_11864.2]

/-- Complete interval computation for depth 15, residue 11865. -/
theorem bounds_15_11865 : exactInterval 15 11865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11865 : oddCount 11865 15 = 8 ∧ acceleratedOrbit 15 11865 = 2377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11865) = 3 ^ 8 * m + 2377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11865.1, data_15_11865.2]

/-- Complete interval computation for depth 15, residue 11866. -/
theorem bounds_15_11866 : exactInterval 15 11866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11866 : oddCount 11866 15 = 6 ∧ acceleratedOrbit 15 11866 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11866) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11866.1, data_15_11866.2]

/-- Complete interval computation for depth 15, residue 11867. -/
theorem bounds_15_11867 : exactInterval 15 11867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11867 : oddCount 11867 15 = 9 ∧ acceleratedOrbit 15 11867 = 7130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11867) = 3 ^ 9 * m + 7130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11867.1, data_15_11867.2]

/-- Complete interval computation for depth 15, residue 11868. -/
theorem bounds_15_11868 : exactInterval 15 11868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11868 : oddCount 11868 15 = 6 ∧ acceleratedOrbit 15 11868 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11868) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11868.1, data_15_11868.2]

/-- Complete interval computation for depth 15, residue 11869. -/
theorem bounds_15_11869 : exactInterval 15 11869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11869 : oddCount 11869 15 = 6 ∧ acceleratedOrbit 15 11869 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11869) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11869.1, data_15_11869.2]

/-- Complete interval computation for depth 15, residue 11870. -/
theorem bounds_15_11870 : exactInterval 15 11870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11870 : oddCount 11870 15 = 8 ∧ acceleratedOrbit 15 11870 = 2378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11870) = 3 ^ 8 * m + 2378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11870.1, data_15_11870.2]

/-- Complete interval computation for depth 15, residue 11871. -/
theorem bounds_15_11871 : exactInterval 15 11871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11871 : oddCount 11871 15 = 8 ∧ acceleratedOrbit 15 11871 = 2378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11871) = 3 ^ 8 * m + 2378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11871.1, data_15_11871.2]

/-- Complete interval computation for depth 15, residue 11872. -/
theorem bounds_15_11872 : exactInterval 15 11872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11872 : oddCount 11872 15 = 5 ∧ acceleratedOrbit 15 11872 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11872) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11872.1, data_15_11872.2]

/-- Complete interval computation for depth 15, residue 11873. -/
theorem bounds_15_11873 : exactInterval 15 11873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11873 : oddCount 11873 15 = 7 ∧ acceleratedOrbit 15 11873 = 793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11873) = 3 ^ 7 * m + 793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11873.1, data_15_11873.2]

/-- Complete interval computation for depth 15, residue 11874. -/
theorem bounds_15_11874 : exactInterval 15 11874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11874 : oddCount 11874 15 = 6 ∧ acceleratedOrbit 15 11874 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11874) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11874.1, data_15_11874.2]

/-- Complete interval computation for depth 15, residue 11875. -/
theorem bounds_15_11875 : exactInterval 15 11875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11875 : oddCount 11875 15 = 6 ∧ acceleratedOrbit 15 11875 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11875) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11875.1, data_15_11875.2]

/-- Complete interval computation for depth 15, residue 11876. -/
theorem bounds_15_11876 : exactInterval 15 11876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11876 : oddCount 11876 15 = 6 ∧ acceleratedOrbit 15 11876 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11876) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11876.1, data_15_11876.2]

/-- Complete interval computation for depth 15, residue 11877. -/
theorem bounds_15_11877 : exactInterval 15 11877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11877 : oddCount 11877 15 = 6 ∧ acceleratedOrbit 15 11877 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11877) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11877.1, data_15_11877.2]

/-- Complete interval computation for depth 15, residue 11878. -/
theorem bounds_15_11878 : exactInterval 15 11878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11878 : oddCount 11878 15 = 6 ∧ acceleratedOrbit 15 11878 = 265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11878) = 3 ^ 6 * m + 265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11878.1, data_15_11878.2]

/-- Complete interval computation for depth 15, residue 11879. -/
theorem bounds_15_11879 : exactInterval 15 11879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11879 : oddCount 11879 15 = 10 ∧ acceleratedOrbit 15 11879 = 21410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11879) = 3 ^ 10 * m + 21410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11879.1, data_15_11879.2]

/-- Complete interval computation for depth 15, residue 11880. -/
theorem bounds_15_11880 : exactInterval 15 11880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11880 : oddCount 11880 15 = 5 ∧ acceleratedOrbit 15 11880 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11880) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11880.1, data_15_11880.2]

/-- Complete interval computation for depth 15, residue 11881. -/
theorem bounds_15_11881 : exactInterval 15 11881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11881 : oddCount 11881 15 = 9 ∧ acceleratedOrbit 15 11881 = 7138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11881) = 3 ^ 9 * m + 7138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11881.1, data_15_11881.2]

/-- Complete interval computation for depth 15, residue 11882. -/
theorem bounds_15_11882 : exactInterval 15 11882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11882 : oddCount 11882 15 = 5 ∧ acceleratedOrbit 15 11882 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11882) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11882.1, data_15_11882.2]

/-- Complete interval computation for depth 15, residue 11883. -/
theorem bounds_15_11883 : exactInterval 15 11883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11883 : oddCount 11883 15 = 8 ∧ acceleratedOrbit 15 11883 = 2380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11883) = 3 ^ 8 * m + 2380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11883.1, data_15_11883.2]

/-- Complete interval computation for depth 15, residue 11884. -/
theorem bounds_15_11884 : exactInterval 15 11884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11884 : oddCount 11884 15 = 7 ∧ acceleratedOrbit 15 11884 = 794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11884) = 3 ^ 7 * m + 794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11884.1, data_15_11884.2]

/-- Complete interval computation for depth 15, residue 11885. -/
theorem bounds_15_11885 : exactInterval 15 11885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11885 : oddCount 11885 15 = 7 ∧ acceleratedOrbit 15 11885 = 794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11885) = 3 ^ 7 * m + 794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11885.1, data_15_11885.2]

/-- Complete interval computation for depth 15, residue 11886. -/
theorem bounds_15_11886 : exactInterval 15 11886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11886 : oddCount 11886 15 = 7 ∧ acceleratedOrbit 15 11886 = 794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11886) = 3 ^ 7 * m + 794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11886.1, data_15_11886.2]

/-- Complete interval computation for depth 15, residue 11887. -/
theorem bounds_15_11887 : exactInterval 15 11887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11887 : oddCount 11887 15 = 10 ∧ acceleratedOrbit 15 11887 = 21424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11887) = 3 ^ 10 * m + 21424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11887.1, data_15_11887.2]

/-- Complete interval computation for depth 15, residue 11888. -/
theorem bounds_15_11888 : exactInterval 15 11888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11888 : oddCount 11888 15 = 9 ∧ acceleratedOrbit 15 11888 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11888) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11888.1, data_15_11888.2]

/-- Complete interval computation for depth 15, residue 11889. -/
theorem bounds_15_11889 : exactInterval 15 11889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11889 : oddCount 11889 15 = 5 ∧ acceleratedOrbit 15 11889 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11889) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11889.1, data_15_11889.2]

/-- Complete interval computation for depth 15, residue 11890. -/
theorem bounds_15_11890 : exactInterval 15 11890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11890 : oddCount 11890 15 = 7 ∧ acceleratedOrbit 15 11890 = 794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11890) = 3 ^ 7 * m + 794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11890.1, data_15_11890.2]

/-- Complete interval computation for depth 15, residue 11891. -/
theorem bounds_15_11891 : exactInterval 15 11891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11891 : oddCount 11891 15 = 7 ∧ acceleratedOrbit 15 11891 = 794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11891) = 3 ^ 7 * m + 794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11891.1, data_15_11891.2]

/-- Complete interval computation for depth 15, residue 11892. -/
theorem bounds_15_11892 : exactInterval 15 11892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11892 : oddCount 11892 15 = 9 ∧ acceleratedOrbit 15 11892 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11892) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11892.1, data_15_11892.2]

/-- Complete interval computation for depth 15, residue 11893. -/
theorem bounds_15_11893 : exactInterval 15 11893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11893 : oddCount 11893 15 = 9 ∧ acceleratedOrbit 15 11893 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11893) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11893.1, data_15_11893.2]

end Collatz.Research.PassageAtlas.Batch0363
