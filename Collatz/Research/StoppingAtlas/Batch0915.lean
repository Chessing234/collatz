import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0915

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6871. -/
theorem bounds_13_6871 : exactInterval 13 6871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6871 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6871) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6871 : oddCount 6871 13 = 8 ∧ acceleratedOrbit 13 6871 = 5507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6871 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6871) = 3 ^ 8 * m + 5507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6871.1, data_13_6871.2]

/-- Complete interval computation for depth 13, residue 6872. -/
theorem bounds_13_6872 : exactInterval 13 6872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6872 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6872) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6872 : oddCount 6872 13 = 7 ∧ acceleratedOrbit 13 6872 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6872 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6872) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6872.1, data_13_6872.2]

/-- Complete interval computation for depth 13, residue 6873. -/
theorem bounds_13_6873 : exactInterval 13 6873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6873 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6873) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6873 : oddCount 6873 13 = 4 ∧ acceleratedOrbit 13 6873 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6873 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6873) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6873.1, data_13_6873.2]

/-- Complete interval computation for depth 13, residue 6874. -/
theorem bounds_13_6874 : exactInterval 13 6874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6874 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6874) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6874 : oddCount 6874 13 = 7 ∧ acceleratedOrbit 13 6874 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6874 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6874) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6874.1, data_13_6874.2]

/-- Complete interval computation for depth 13, residue 6875. -/
theorem bounds_13_6875 : exactInterval 13 6875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6875 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6875) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6875 : oddCount 6875 13 = 10 ∧ acceleratedOrbit 13 6875 = 49571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6875 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6875) = 3 ^ 10 * m + 49571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6875.1, data_13_6875.2]

/-- Complete interval computation for depth 13, residue 6876. -/
theorem bounds_13_6876 : exactInterval 13 6876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6876 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6876) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6876 : oddCount 6876 13 = 7 ∧ acceleratedOrbit 13 6876 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6876 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6876) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6876.1, data_13_6876.2]

/-- Complete interval computation for depth 13, residue 6877. -/
theorem bounds_13_6877 : exactInterval 13 6877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6877 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6877) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6877 : oddCount 6877 13 = 7 ∧ acceleratedOrbit 13 6877 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6877 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6877) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6877.1, data_13_6877.2]

/-- Complete interval computation for depth 13, residue 6878. -/
theorem bounds_13_6878 : exactInterval 13 6878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6878 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6878) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6878 : oddCount 6878 13 = 7 ∧ acceleratedOrbit 13 6878 = 1837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6878 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6878) = 3 ^ 7 * m + 1837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6878.1, data_13_6878.2]

/-- Complete interval computation for depth 13, residue 6879. -/
theorem bounds_13_6879 : exactInterval 13 6879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6879 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6879) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6879 : oddCount 6879 13 = 7 ∧ acceleratedOrbit 13 6879 = 1837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6879 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6879) = 3 ^ 7 * m + 1837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6879.1, data_13_6879.2]

/-- Complete interval computation for depth 13, residue 6880. -/
theorem bounds_13_6880 : exactInterval 13 6880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6880 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6880) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6880 : oddCount 6880 13 = 5 ∧ acceleratedOrbit 13 6880 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6880 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6880) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6880.1, data_13_6880.2]

/-- Complete interval computation for depth 13, residue 6881. -/
theorem bounds_13_6881 : exactInterval 13 6881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6881 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6881) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6881 : oddCount 6881 13 = 8 ∧ acceleratedOrbit 13 6881 = 5513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6881 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6881) = 3 ^ 8 * m + 5513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6881.1, data_13_6881.2]

/-- Complete interval computation for depth 13, residue 6882. -/
theorem bounds_13_6882 : exactInterval 13 6882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6882 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6882) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6882 : oddCount 6882 13 = 5 ∧ acceleratedOrbit 13 6882 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6882 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6882) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6882.1, data_13_6882.2]

/-- Complete interval computation for depth 13, residue 6883. -/
theorem bounds_13_6883 : exactInterval 13 6883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6883 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6883) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6883 : oddCount 6883 13 = 5 ∧ acceleratedOrbit 13 6883 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6883 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6883) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6883.1, data_13_6883.2]

/-- Complete interval computation for depth 13, residue 6884. -/
theorem bounds_13_6884 : exactInterval 13 6884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6884 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6884) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6884 : oddCount 6884 13 = 6 ∧ acceleratedOrbit 13 6884 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6884 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6884) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6884.1, data_13_6884.2]

/-- Complete interval computation for depth 13, residue 6885. -/
theorem bounds_13_6885 : exactInterval 13 6885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6885 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6885) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6885 : oddCount 6885 13 = 6 ∧ acceleratedOrbit 13 6885 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6885 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6885) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6885.1, data_13_6885.2]

end Collatz.Research.StoppingAtlas.Batch0915
