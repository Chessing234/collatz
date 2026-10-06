import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0546

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17858. -/
theorem bounds_15_17858 : exactInterval 15 17858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17858 : oddCount 17858 15 = 9 ∧ acceleratedOrbit 15 17858 = 10730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17858) = 3 ^ 9 * m + 10730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17858.1, data_15_17858.2]

/-- Complete interval computation for depth 15, residue 17859. -/
theorem bounds_15_17859 : exactInterval 15 17859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17859 : oddCount 17859 15 = 9 ∧ acceleratedOrbit 15 17859 = 10730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17859) = 3 ^ 9 * m + 10730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17859.1, data_15_17859.2]

/-- Complete interval computation for depth 15, residue 17860. -/
theorem bounds_15_17860 : exactInterval 15 17860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17860 : oddCount 17860 15 = 5 ∧ acceleratedOrbit 15 17860 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17860) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17860.1, data_15_17860.2]

/-- Complete interval computation for depth 15, residue 17861. -/
theorem bounds_15_17861 : exactInterval 15 17861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17861 : oddCount 17861 15 = 5 ∧ acceleratedOrbit 15 17861 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17861) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17861.1, data_15_17861.2]

/-- Complete interval computation for depth 15, residue 17862. -/
theorem bounds_15_17862 : exactInterval 15 17862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17862 : oddCount 17862 15 = 5 ∧ acceleratedOrbit 15 17862 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17862) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17862.1, data_15_17862.2]

/-- Complete interval computation for depth 15, residue 17863. -/
theorem bounds_15_17863 : exactInterval 15 17863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17863 : oddCount 17863 15 = 9 ∧ acceleratedOrbit 15 17863 = 10732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17863) = 3 ^ 9 * m + 10732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17863.1, data_15_17863.2]

/-- Complete interval computation for depth 15, residue 17864. -/
theorem bounds_15_17864 : exactInterval 15 17864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17864 : oddCount 17864 15 = 6 ∧ acceleratedOrbit 15 17864 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17864) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17864.1, data_15_17864.2]

/-- Complete interval computation for depth 15, residue 17865. -/
theorem bounds_15_17865 : exactInterval 15 17865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17865 : oddCount 17865 15 = 6 ∧ acceleratedOrbit 15 17865 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17865) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17865.1, data_15_17865.2]

/-- Complete interval computation for depth 15, residue 17866. -/
theorem bounds_15_17866 : exactInterval 15 17866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17866 : oddCount 17866 15 = 6 ∧ acceleratedOrbit 15 17866 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17866) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17866.1, data_15_17866.2]

/-- Complete interval computation for depth 15, residue 17867. -/
theorem bounds_15_17867 : exactInterval 15 17867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17867 : oddCount 17867 15 = 7 ∧ acceleratedOrbit 15 17867 = 1193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17867) = 3 ^ 7 * m + 1193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17867.1, data_15_17867.2]

/-- Complete interval computation for depth 15, residue 17868. -/
theorem bounds_15_17868 : exactInterval 15 17868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17868 : oddCount 17868 15 = 6 ∧ acceleratedOrbit 15 17868 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17868) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17868.1, data_15_17868.2]

/-- Complete interval computation for depth 15, residue 17869. -/
theorem bounds_15_17869 : exactInterval 15 17869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17869 : oddCount 17869 15 = 6 ∧ acceleratedOrbit 15 17869 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17869) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17869.1, data_15_17869.2]

/-- Complete interval computation for depth 15, residue 17870. -/
theorem bounds_15_17870 : exactInterval 15 17870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17870 : oddCount 17870 15 = 11 ∧ acceleratedOrbit 15 17870 = 96623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17870) = 3 ^ 11 * m + 96623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17870.1, data_15_17870.2]

/-- Complete interval computation for depth 15, residue 17871. -/
theorem bounds_15_17871 : exactInterval 15 17871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17871 : oddCount 17871 15 = 11 ∧ acceleratedOrbit 15 17871 = 96623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17871) = 3 ^ 11 * m + 96623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17871.1, data_15_17871.2]

/-- Complete interval computation for depth 15, residue 17872. -/
theorem bounds_15_17872 : exactInterval 15 17872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17872 : oddCount 17872 15 = 5 ∧ acceleratedOrbit 15 17872 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17872) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17872.1, data_15_17872.2]

/-- Complete interval computation for depth 15, residue 17873. -/
theorem bounds_15_17873 : exactInterval 15 17873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17873 : oddCount 17873 15 = 6 ∧ acceleratedOrbit 15 17873 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17873) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17873.1, data_15_17873.2]

/-- Complete interval computation for depth 15, residue 17874. -/
theorem bounds_15_17874 : exactInterval 15 17874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17874 : oddCount 17874 15 = 9 ∧ acceleratedOrbit 15 17874 = 10739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17874) = 3 ^ 9 * m + 10739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17874.1, data_15_17874.2]

/-- Complete interval computation for depth 15, residue 17875. -/
theorem bounds_15_17875 : exactInterval 15 17875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17875 : oddCount 17875 15 = 9 ∧ acceleratedOrbit 15 17875 = 10739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17875) = 3 ^ 9 * m + 10739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17875.1, data_15_17875.2]

/-- Complete interval computation for depth 15, residue 17876. -/
theorem bounds_15_17876 : exactInterval 15 17876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17876 : oddCount 17876 15 = 5 ∧ acceleratedOrbit 15 17876 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17876) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17876.1, data_15_17876.2]

/-- Complete interval computation for depth 15, residue 17877. -/
theorem bounds_15_17877 : exactInterval 15 17877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17877 : oddCount 17877 15 = 5 ∧ acceleratedOrbit 15 17877 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17877) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17877.1, data_15_17877.2]

/-- Complete interval computation for depth 15, residue 17878. -/
theorem bounds_15_17878 : exactInterval 15 17878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17878 : oddCount 17878 15 = 8 ∧ acceleratedOrbit 15 17878 = 3581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17878) = 3 ^ 8 * m + 3581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17878.1, data_15_17878.2]

/-- Complete interval computation for depth 15, residue 17879. -/
theorem bounds_15_17879 : exactInterval 15 17879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17879 : oddCount 17879 15 = 8 ∧ acceleratedOrbit 15 17879 = 3581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17879) = 3 ^ 8 * m + 3581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17879.1, data_15_17879.2]

/-- Complete interval computation for depth 15, residue 17880. -/
theorem bounds_15_17880 : exactInterval 15 17880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17880 : oddCount 17880 15 = 8 ∧ acceleratedOrbit 15 17880 = 3584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17880) = 3 ^ 8 * m + 3584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17880.1, data_15_17880.2]

/-- Complete interval computation for depth 15, residue 17881. -/
theorem bounds_15_17881 : exactInterval 15 17881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17881 : oddCount 17881 15 = 8 ∧ acceleratedOrbit 15 17881 = 3584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17881) = 3 ^ 8 * m + 3584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17881.1, data_15_17881.2]

/-- Complete interval computation for depth 15, residue 17882. -/
theorem bounds_15_17882 : exactInterval 15 17882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17882 : oddCount 17882 15 = 8 ∧ acceleratedOrbit 15 17882 = 3584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17882) = 3 ^ 8 * m + 3584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17882.1, data_15_17882.2]

/-- Complete interval computation for depth 15, residue 17883. -/
theorem bounds_15_17883 : exactInterval 15 17883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17883 : oddCount 17883 15 = 6 ∧ acceleratedOrbit 15 17883 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17883) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17883.1, data_15_17883.2]

/-- Complete interval computation for depth 15, residue 17884. -/
theorem bounds_15_17884 : exactInterval 15 17884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17884 : oddCount 17884 15 = 8 ∧ acceleratedOrbit 15 17884 = 3584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17884) = 3 ^ 8 * m + 3584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17884.1, data_15_17884.2]

/-- Complete interval computation for depth 15, residue 17885. -/
theorem bounds_15_17885 : exactInterval 15 17885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17885 : oddCount 17885 15 = 8 ∧ acceleratedOrbit 15 17885 = 3584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17885) = 3 ^ 8 * m + 3584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17885.1, data_15_17885.2]

/-- Complete interval computation for depth 15, residue 17886. -/
theorem bounds_15_17886 : exactInterval 15 17886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17886 : oddCount 17886 15 = 11 ∧ acceleratedOrbit 15 17886 = 96707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17886) = 3 ^ 11 * m + 96707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17886.1, data_15_17886.2]

/-- Complete interval computation for depth 15, residue 17887. -/
theorem bounds_15_17887 : exactInterval 15 17887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17887 : oddCount 17887 15 = 11 ∧ acceleratedOrbit 15 17887 = 96707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17887) = 3 ^ 11 * m + 96707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17887.1, data_15_17887.2]

/-- Complete interval computation for depth 15, residue 17888. -/
theorem bounds_15_17888 : exactInterval 15 17888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17888 : oddCount 17888 15 = 8 ∧ acceleratedOrbit 15 17888 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17888) = 3 ^ 8 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17888.1, data_15_17888.2]

/-- Complete interval computation for depth 15, residue 17889. -/
theorem bounds_15_17889 : exactInterval 15 17889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17889 : oddCount 17889 15 = 9 ∧ acceleratedOrbit 15 17889 = 10748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17889) = 3 ^ 9 * m + 10748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17889.1, data_15_17889.2]

/-- Complete interval computation for depth 15, residue 17890. -/
theorem bounds_15_17890 : exactInterval 15 17890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17890 : oddCount 17890 15 = 5 ∧ acceleratedOrbit 15 17890 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17890) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17890.1, data_15_17890.2]

end Collatz.Research.PassageAtlas.Batch0546
