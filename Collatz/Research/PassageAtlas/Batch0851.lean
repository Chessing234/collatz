import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0851

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27852. -/
theorem bounds_15_27852 : exactInterval 15 27852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27852 : oddCount 27852 15 = 7 ∧ acceleratedOrbit 15 27852 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27852) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27852.1, data_15_27852.2]

/-- Complete interval computation for depth 15, residue 27853. -/
theorem bounds_15_27853 : exactInterval 15 27853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27853 : oddCount 27853 15 = 7 ∧ acceleratedOrbit 15 27853 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27853) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27853.1, data_15_27853.2]

/-- Complete interval computation for depth 15, residue 27854. -/
theorem bounds_15_27854 : exactInterval 15 27854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27854 : oddCount 27854 15 = 9 ∧ acceleratedOrbit 15 27854 = 16733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27854) = 3 ^ 9 * m + 16733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27854.1, data_15_27854.2]

/-- Complete interval computation for depth 15, residue 27855. -/
theorem bounds_15_27855 : exactInterval 15 27855 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27855) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27855 : oddCount 27855 15 = 9 ∧ acceleratedOrbit 15 27855 = 16733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27855) = 3 ^ 9 * m + 16733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27855.1, data_15_27855.2]

/-- Complete interval computation for depth 15, residue 27856. -/
theorem bounds_15_27856 : exactInterval 15 27856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27856 : oddCount 27856 15 = 3 ∧ acceleratedOrbit 15 27856 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27856) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27856.1, data_15_27856.2]

/-- Complete interval computation for depth 15, residue 27857. -/
theorem bounds_15_27857 : exactInterval 15 27857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27857 : oddCount 27857 15 = 10 ∧ acceleratedOrbit 15 27857 = 50210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27857) = 3 ^ 10 * m + 50210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27857.1, data_15_27857.2]

/-- Complete interval computation for depth 15, residue 27858. -/
theorem bounds_15_27858 : exactInterval 15 27858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27858 : oddCount 27858 15 = 10 ∧ acceleratedOrbit 15 27858 = 50210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27858) = 3 ^ 10 * m + 50210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27858.1, data_15_27858.2]

/-- Complete interval computation for depth 15, residue 27859. -/
theorem bounds_15_27859 : exactInterval 15 27859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27859 : oddCount 27859 15 = 10 ∧ acceleratedOrbit 15 27859 = 50210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27859) = 3 ^ 10 * m + 50210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27859.1, data_15_27859.2]

/-- Complete interval computation for depth 15, residue 27860. -/
theorem bounds_15_27860 : exactInterval 15 27860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27860 : oddCount 27860 15 = 3 ∧ acceleratedOrbit 15 27860 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27860) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27860.1, data_15_27860.2]

/-- Complete interval computation for depth 15, residue 27861. -/
theorem bounds_15_27861 : exactInterval 15 27861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27861 : oddCount 27861 15 = 3 ∧ acceleratedOrbit 15 27861 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27861) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27861.1, data_15_27861.2]

/-- Complete interval computation for depth 15, residue 27862. -/
theorem bounds_15_27862 : exactInterval 15 27862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27862 : oddCount 27862 15 = 10 ∧ acceleratedOrbit 15 27862 = 50219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27862) = 3 ^ 10 * m + 50219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27862.1, data_15_27862.2]

/-- Complete interval computation for depth 15, residue 27863. -/
theorem bounds_15_27863 : exactInterval 15 27863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27863 : oddCount 27863 15 = 10 ∧ acceleratedOrbit 15 27863 = 50219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27863) = 3 ^ 10 * m + 50219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27863.1, data_15_27863.2]

/-- Complete interval computation for depth 15, residue 27864. -/
theorem bounds_15_27864 : exactInterval 15 27864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27864 : oddCount 27864 15 = 8 ∧ acceleratedOrbit 15 27864 = 5582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27864) = 3 ^ 8 * m + 5582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27864.1, data_15_27864.2]

/-- Complete interval computation for depth 15, residue 27865. -/
theorem bounds_15_27865 : exactInterval 15 27865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27865 : oddCount 27865 15 = 8 ∧ acceleratedOrbit 15 27865 = 5582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27865) = 3 ^ 8 * m + 5582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27865.1, data_15_27865.2]

/-- Complete interval computation for depth 15, residue 27866. -/
theorem bounds_15_27866 : exactInterval 15 27866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27866 : oddCount 27866 15 = 8 ∧ acceleratedOrbit 15 27866 = 5582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27866) = 3 ^ 8 * m + 5582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27866.1, data_15_27866.2]

/-- Complete interval computation for depth 15, residue 27867. -/
theorem bounds_15_27867 : exactInterval 15 27867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27867 : oddCount 27867 15 = 6 ∧ acceleratedOrbit 15 27867 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27867) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27867.1, data_15_27867.2]

/-- Complete interval computation for depth 15, residue 27868. -/
theorem bounds_15_27868 : exactInterval 15 27868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27868 : oddCount 27868 15 = 8 ∧ acceleratedOrbit 15 27868 = 5582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27868) = 3 ^ 8 * m + 5582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27868.1, data_15_27868.2]

/-- Complete interval computation for depth 15, residue 27869. -/
theorem bounds_15_27869 : exactInterval 15 27869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27869 : oddCount 27869 15 = 8 ∧ acceleratedOrbit 15 27869 = 5582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27869) = 3 ^ 8 * m + 5582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27869.1, data_15_27869.2]

/-- Complete interval computation for depth 15, residue 27870. -/
theorem bounds_15_27870 : exactInterval 15 27870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27870 : oddCount 27870 15 = 8 ∧ acceleratedOrbit 15 27870 = 5581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27870) = 3 ^ 8 * m + 5581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27870.1, data_15_27870.2]

/-- Complete interval computation for depth 15, residue 27871. -/
theorem bounds_15_27871 : exactInterval 15 27871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27871 : oddCount 27871 15 = 8 ∧ acceleratedOrbit 15 27871 = 5581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27871) = 3 ^ 8 * m + 5581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27871.1, data_15_27871.2]

/-- Complete interval computation for depth 15, residue 27872. -/
theorem bounds_15_27872 : exactInterval 15 27872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27872 : oddCount 27872 15 = 9 ∧ acceleratedOrbit 15 27872 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27872) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27872.1, data_15_27872.2]

/-- Complete interval computation for depth 15, residue 27873. -/
theorem bounds_15_27873 : exactInterval 15 27873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27873 : oddCount 27873 15 = 10 ∧ acceleratedOrbit 15 27873 = 50233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27873) = 3 ^ 10 * m + 50233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27873.1, data_15_27873.2]

/-- Complete interval computation for depth 15, residue 27874. -/
theorem bounds_15_27874 : exactInterval 15 27874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27874 : oddCount 27874 15 = 3 ∧ acceleratedOrbit 15 27874 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27874) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27874.1, data_15_27874.2]

/-- Complete interval computation for depth 15, residue 27875. -/
theorem bounds_15_27875 : exactInterval 15 27875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27875 : oddCount 27875 15 = 3 ∧ acceleratedOrbit 15 27875 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27875) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27875.1, data_15_27875.2]

/-- Complete interval computation for depth 15, residue 27876. -/
theorem bounds_15_27876 : exactInterval 15 27876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27876 : oddCount 27876 15 = 8 ∧ acceleratedOrbit 15 27876 = 5584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27876) = 3 ^ 8 * m + 5584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27876.1, data_15_27876.2]

/-- Complete interval computation for depth 15, residue 27877. -/
theorem bounds_15_27877 : exactInterval 15 27877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27877 : oddCount 27877 15 = 8 ∧ acceleratedOrbit 15 27877 = 5584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27877) = 3 ^ 8 * m + 5584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27877.1, data_15_27877.2]

/-- Complete interval computation for depth 15, residue 27878. -/
theorem bounds_15_27878 : exactInterval 15 27878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27878 : oddCount 27878 15 = 8 ∧ acceleratedOrbit 15 27878 = 5584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27878) = 3 ^ 8 * m + 5584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27878.1, data_15_27878.2]

/-- Complete interval computation for depth 15, residue 27879. -/
theorem bounds_15_27879 : exactInterval 15 27879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27879 : oddCount 27879 15 = 10 ∧ acceleratedOrbit 15 27879 = 50242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27879) = 3 ^ 10 * m + 50242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27879.1, data_15_27879.2]

/-- Complete interval computation for depth 15, residue 27880. -/
theorem bounds_15_27880 : exactInterval 15 27880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27880 : oddCount 27880 15 = 9 ∧ acceleratedOrbit 15 27880 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27880) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27880.1, data_15_27880.2]

/-- Complete interval computation for depth 15, residue 27881. -/
theorem bounds_15_27881 : exactInterval 15 27881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27881 : oddCount 27881 15 = 7 ∧ acceleratedOrbit 15 27881 = 1861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27881) = 3 ^ 7 * m + 1861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27881.1, data_15_27881.2]

/-- Complete interval computation for depth 15, residue 27882. -/
theorem bounds_15_27882 : exactInterval 15 27882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27882 : oddCount 27882 15 = 9 ∧ acceleratedOrbit 15 27882 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27882) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27882.1, data_15_27882.2]

/-- Complete interval computation for depth 15, residue 27883. -/
theorem bounds_15_27883 : exactInterval 15 27883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27883 : oddCount 27883 15 = 9 ∧ acceleratedOrbit 15 27883 = 16750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27883) = 3 ^ 9 * m + 16750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27883.1, data_15_27883.2]

/-- Complete interval computation for depth 15, residue 27884. -/
theorem bounds_15_27884 : exactInterval 15 27884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27884 : oddCount 27884 15 = 8 ∧ acceleratedOrbit 15 27884 = 5588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27884) = 3 ^ 8 * m + 5588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27884.1, data_15_27884.2]

end Collatz.Research.PassageAtlas.Batch0851
