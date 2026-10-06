import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0668

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21856. -/
theorem bounds_15_21856 : exactInterval 15 21856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21856 : oddCount 21856 15 = 6 ∧ acceleratedOrbit 15 21856 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21856) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21856.1, data_15_21856.2]

/-- Complete interval computation for depth 15, residue 21857. -/
theorem bounds_15_21857 : exactInterval 15 21857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21857 : oddCount 21857 15 = 7 ∧ acceleratedOrbit 15 21857 = 1459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21857) = 3 ^ 7 * m + 1459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21857.1, data_15_21857.2]

/-- Complete interval computation for depth 15, residue 21858. -/
theorem bounds_15_21858 : exactInterval 15 21858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21858 : oddCount 21858 15 = 6 ∧ acceleratedOrbit 15 21858 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21858) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21858.1, data_15_21858.2]

/-- Complete interval computation for depth 15, residue 21859. -/
theorem bounds_15_21859 : exactInterval 15 21859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21859 : oddCount 21859 15 = 6 ∧ acceleratedOrbit 15 21859 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21859) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21859.1, data_15_21859.2]

/-- Complete interval computation for depth 15, residue 21860. -/
theorem bounds_15_21860 : exactInterval 15 21860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21860 : oddCount 21860 15 = 6 ∧ acceleratedOrbit 15 21860 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21860) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21860.1, data_15_21860.2]

/-- Complete interval computation for depth 15, residue 21861. -/
theorem bounds_15_21861 : exactInterval 15 21861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21861 : oddCount 21861 15 = 6 ∧ acceleratedOrbit 15 21861 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21861) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21861.1, data_15_21861.2]

/-- Complete interval computation for depth 15, residue 21862. -/
theorem bounds_15_21862 : exactInterval 15 21862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21862 : oddCount 21862 15 = 6 ∧ acceleratedOrbit 15 21862 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21862) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21862.1, data_15_21862.2]

/-- Complete interval computation for depth 15, residue 21863. -/
theorem bounds_15_21863 : exactInterval 15 21863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21863 : oddCount 21863 15 = 11 ∧ acceleratedOrbit 15 21863 = 118201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21863) = 3 ^ 11 * m + 118201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21863.1, data_15_21863.2]

/-- Complete interval computation for depth 15, residue 21864. -/
theorem bounds_15_21864 : exactInterval 15 21864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21864 : oddCount 21864 15 = 6 ∧ acceleratedOrbit 15 21864 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21864) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21864.1, data_15_21864.2]

/-- Complete interval computation for depth 15, residue 21865. -/
theorem bounds_15_21865 : exactInterval 15 21865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21865 : oddCount 21865 15 = 7 ∧ acceleratedOrbit 15 21865 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21865) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21865.1, data_15_21865.2]

/-- Complete interval computation for depth 15, residue 21866. -/
theorem bounds_15_21866 : exactInterval 15 21866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21866 : oddCount 21866 15 = 6 ∧ acceleratedOrbit 15 21866 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21866) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21866.1, data_15_21866.2]

/-- Complete interval computation for depth 15, residue 21867. -/
theorem bounds_15_21867 : exactInterval 15 21867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21867 : oddCount 21867 15 = 8 ∧ acceleratedOrbit 15 21867 = 4379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21867) = 3 ^ 8 * m + 4379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21867.1, data_15_21867.2]

/-- Complete interval computation for depth 15, residue 21868. -/
theorem bounds_15_21868 : exactInterval 15 21868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21868 : oddCount 21868 15 = 7 ∧ acceleratedOrbit 15 21868 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21868) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21868.1, data_15_21868.2]

/-- Complete interval computation for depth 15, residue 21869. -/
theorem bounds_15_21869 : exactInterval 15 21869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21869 : oddCount 21869 15 = 7 ∧ acceleratedOrbit 15 21869 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21869) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21869.1, data_15_21869.2]

/-- Complete interval computation for depth 15, residue 21870. -/
theorem bounds_15_21870 : exactInterval 15 21870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21870 : oddCount 21870 15 = 7 ∧ acceleratedOrbit 15 21870 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21870) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21870.1, data_15_21870.2]

/-- Complete interval computation for depth 15, residue 21871. -/
theorem bounds_15_21871 : exactInterval 15 21871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21871 : oddCount 21871 15 = 9 ∧ acceleratedOrbit 15 21871 = 13139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21871) = 3 ^ 9 * m + 13139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21871.1, data_15_21871.2]

/-- Complete interval computation for depth 15, residue 21872. -/
theorem bounds_15_21872 : exactInterval 15 21872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21872 : oddCount 21872 15 = 6 ∧ acceleratedOrbit 15 21872 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21872) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21872.1, data_15_21872.2]

/-- Complete interval computation for depth 15, residue 21873. -/
theorem bounds_15_21873 : exactInterval 15 21873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21873 : oddCount 21873 15 = 6 ∧ acceleratedOrbit 15 21873 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21873) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21873.1, data_15_21873.2]

/-- Complete interval computation for depth 15, residue 21874. -/
theorem bounds_15_21874 : exactInterval 15 21874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21874 : oddCount 21874 15 = 6 ∧ acceleratedOrbit 15 21874 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21874) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21874.1, data_15_21874.2]

/-- Complete interval computation for depth 15, residue 21875. -/
theorem bounds_15_21875 : exactInterval 15 21875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21875 : oddCount 21875 15 = 6 ∧ acceleratedOrbit 15 21875 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21875) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21875.1, data_15_21875.2]

/-- Complete interval computation for depth 15, residue 21876. -/
theorem bounds_15_21876 : exactInterval 15 21876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21876 : oddCount 21876 15 = 6 ∧ acceleratedOrbit 15 21876 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21876) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21876.1, data_15_21876.2]

/-- Complete interval computation for depth 15, residue 21877. -/
theorem bounds_15_21877 : exactInterval 15 21877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21877 : oddCount 21877 15 = 6 ∧ acceleratedOrbit 15 21877 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21877) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21877.1, data_15_21877.2]

/-- Complete interval computation for depth 15, residue 21878. -/
theorem bounds_15_21878 : exactInterval 15 21878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21878 : oddCount 21878 15 = 8 ∧ acceleratedOrbit 15 21878 = 4382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21878) = 3 ^ 8 * m + 4382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21878.1, data_15_21878.2]

/-- Complete interval computation for depth 15, residue 21879. -/
theorem bounds_15_21879 : exactInterval 15 21879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21879 : oddCount 21879 15 = 8 ∧ acceleratedOrbit 15 21879 = 4382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21879) = 3 ^ 8 * m + 4382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21879.1, data_15_21879.2]

/-- Complete interval computation for depth 15, residue 21880. -/
theorem bounds_15_21880 : exactInterval 15 21880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21880 : oddCount 21880 15 = 6 ∧ acceleratedOrbit 15 21880 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21880) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21880.1, data_15_21880.2]

/-- Complete interval computation for depth 15, residue 21881. -/
theorem bounds_15_21881 : exactInterval 15 21881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21881 : oddCount 21881 15 = 11 ∧ acceleratedOrbit 15 21881 = 118304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21881) = 3 ^ 11 * m + 118304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21881.1, data_15_21881.2]

/-- Complete interval computation for depth 15, residue 21882. -/
theorem bounds_15_21882 : exactInterval 15 21882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21882 : oddCount 21882 15 = 6 ∧ acceleratedOrbit 15 21882 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21882) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21882.1, data_15_21882.2]

/-- Complete interval computation for depth 15, residue 21883. -/
theorem bounds_15_21883 : exactInterval 15 21883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21883 : oddCount 21883 15 = 9 ∧ acceleratedOrbit 15 21883 = 13148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21883) = 3 ^ 9 * m + 13148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21883.1, data_15_21883.2]

/-- Complete interval computation for depth 15, residue 21884. -/
theorem bounds_15_21884 : exactInterval 15 21884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21884 : oddCount 21884 15 = 6 ∧ acceleratedOrbit 15 21884 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21884) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21884.1, data_15_21884.2]

/-- Complete interval computation for depth 15, residue 21885. -/
theorem bounds_15_21885 : exactInterval 15 21885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21885 : oddCount 21885 15 = 6 ∧ acceleratedOrbit 15 21885 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21885) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21885.1, data_15_21885.2]

/-- Complete interval computation for depth 15, residue 21886. -/
theorem bounds_15_21886 : exactInterval 15 21886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21886 : oddCount 21886 15 = 11 ∧ acceleratedOrbit 15 21886 = 118331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21886) = 3 ^ 11 * m + 118331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21886.1, data_15_21886.2]

/-- Complete interval computation for depth 15, residue 21887. -/
theorem bounds_15_21887 : exactInterval 15 21887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21887 : oddCount 21887 15 = 11 ∧ acceleratedOrbit 15 21887 = 118331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21887) = 3 ^ 11 * m + 118331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21887.1, data_15_21887.2]

/-- Complete interval computation for depth 15, residue 21888. -/
theorem bounds_15_21888 : exactInterval 15 21888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21888 : oddCount 21888 15 = 5 ∧ acceleratedOrbit 15 21888 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21888) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21888.1, data_15_21888.2]

end Collatz.Research.PassageAtlas.Batch0668
