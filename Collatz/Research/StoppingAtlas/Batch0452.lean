import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0452

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3855. -/
theorem bounds_12_3855 : exactInterval 12 3855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3855 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3855) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3855 : oddCount 3855 12 = 5 ∧ acceleratedOrbit 12 3855 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3855 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3855) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3855.1, data_12_3855.2]

/-- Complete interval computation for depth 12, residue 3856. -/
theorem bounds_12_3856 : exactInterval 12 3856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3856 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3856) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3856 : oddCount 3856 12 = 3 ∧ acceleratedOrbit 12 3856 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3856 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3856) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3856.1, data_12_3856.2]

/-- Complete interval computation for depth 12, residue 3857. -/
theorem bounds_12_3857 : exactInterval 12 3857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3857 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3857) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3857 : oddCount 3857 12 = 6 ∧ acceleratedOrbit 12 3857 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3857 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3857) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3857.1, data_12_3857.2]

/-- Complete interval computation for depth 12, residue 3858. -/
theorem bounds_12_3858 : exactInterval 12 3858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3858 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3858) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3858 : oddCount 3858 12 = 7 ∧ acceleratedOrbit 12 3858 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3858 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3858) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3858.1, data_12_3858.2]

/-- Complete interval computation for depth 12, residue 3859. -/
theorem bounds_12_3859 : exactInterval 12 3859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3859 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3859) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3859 : oddCount 3859 12 = 7 ∧ acceleratedOrbit 12 3859 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3859 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3859) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3859.1, data_12_3859.2]

/-- Complete interval computation for depth 12, residue 3860. -/
theorem bounds_12_3860 : exactInterval 12 3860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3860 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3860) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3860 : oddCount 3860 12 = 3 ∧ acceleratedOrbit 12 3860 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3860 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3860) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3860.1, data_12_3860.2]

/-- Complete interval computation for depth 12, residue 3861. -/
theorem bounds_12_3861 : exactInterval 12 3861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3861 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3861) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3861 : oddCount 3861 12 = 3 ∧ acceleratedOrbit 12 3861 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3861 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3861) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3861.1, data_12_3861.2]

/-- Complete interval computation for depth 12, residue 3862. -/
theorem bounds_12_3862 : exactInterval 12 3862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3862 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3862) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3862 : oddCount 3862 12 = 7 ∧ acceleratedOrbit 12 3862 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3862 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3862) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3862.1, data_12_3862.2]

/-- Complete interval computation for depth 12, residue 3863. -/
theorem bounds_12_3863 : exactInterval 12 3863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3863 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3863) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3863 : oddCount 3863 12 = 7 ∧ acceleratedOrbit 12 3863 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3863 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3863) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3863.1, data_12_3863.2]

/-- Complete interval computation for depth 12, residue 3864. -/
theorem bounds_12_3864 : exactInterval 12 3864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3864 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3864) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3864 : oddCount 3864 12 = 3 ∧ acceleratedOrbit 12 3864 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3864 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3864) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3864.1, data_12_3864.2]

/-- Complete interval computation for depth 12, residue 3865. -/
theorem bounds_12_3865 : exactInterval 12 3865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3865 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3865) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3865 : oddCount 3865 12 = 8 ∧ acceleratedOrbit 12 3865 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3865 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3865) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3865.1, data_12_3865.2]

/-- Complete interval computation for depth 12, residue 3866. -/
theorem bounds_12_3866 : exactInterval 12 3866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3866 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3866) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3866 : oddCount 3866 12 = 3 ∧ acceleratedOrbit 12 3866 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3866 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3866) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3866.1, data_12_3866.2]

/-- Complete interval computation for depth 12, residue 3867. -/
theorem bounds_12_3867 : exactInterval 12 3867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3867 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3867) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3867 : oddCount 3867 12 = 10 ∧ acceleratedOrbit 12 3867 = 55768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3867 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3867) = 3 ^ 10 * m + 55768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3867.1, data_12_3867.2]

/-- Complete interval computation for depth 12, residue 3868. -/
theorem bounds_12_3868 : exactInterval 12 3868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3868 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3868) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3868 : oddCount 3868 12 = 7 ∧ acceleratedOrbit 12 3868 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3868 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3868) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3868.1, data_12_3868.2]

/-- Complete interval computation for depth 12, residue 3869. -/
theorem bounds_12_3869 : exactInterval 12 3869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3869 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3869) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3869 : oddCount 3869 12 = 7 ∧ acceleratedOrbit 12 3869 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3869 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3869) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3869.1, data_12_3869.2]

end Collatz.Research.StoppingAtlas.Batch0452
