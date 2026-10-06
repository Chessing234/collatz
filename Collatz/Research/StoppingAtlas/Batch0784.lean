import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0784

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4858. -/
theorem bounds_13_4858 : exactInterval 13 4858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4858 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4858) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4858 : oddCount 4858 13 = 6 ∧ acceleratedOrbit 13 4858 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4858 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4858) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4858.1, data_13_4858.2]

/-- Complete interval computation for depth 13, residue 4859. -/
theorem bounds_13_4859 : exactInterval 13 4859 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4859 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4859) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4859 : oddCount 4859 13 = 8 ∧ acceleratedOrbit 13 4859 = 3893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4859 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4859) = 3 ^ 8 * m + 3893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4859.1, data_13_4859.2]

/-- Complete interval computation for depth 13, residue 4860. -/
theorem bounds_13_4860 : exactInterval 13 4860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4860 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4860) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4860 : oddCount 4860 13 = 8 ∧ acceleratedOrbit 13 4860 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4860 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4860) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4860.1, data_13_4860.2]

/-- Complete interval computation for depth 13, residue 4861. -/
theorem bounds_13_4861 : exactInterval 13 4861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4861 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4861) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4861 : oddCount 4861 13 = 8 ∧ acceleratedOrbit 13 4861 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4861 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4861) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4861.1, data_13_4861.2]

/-- Complete interval computation for depth 13, residue 4862. -/
theorem bounds_13_4862 : exactInterval 13 4862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4862 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4862) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4862 : oddCount 4862 13 = 8 ∧ acceleratedOrbit 13 4862 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4862 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4862) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4862.1, data_13_4862.2]

/-- Complete interval computation for depth 13, residue 4863. -/
theorem bounds_13_4863 : exactInterval 13 4863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4863 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4863) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4863 : oddCount 4863 13 = 11 ∧ acceleratedOrbit 13 4863 = 105182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4863 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4863) = 3 ^ 11 * m + 105182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4863.1, data_13_4863.2]

/-- Complete interval computation for depth 13, residue 4864. -/
theorem bounds_13_4864 : exactInterval 13 4864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4864 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4864) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4864 : oddCount 4864 13 = 3 ∧ acceleratedOrbit 13 4864 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4864 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4864) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4864.1, data_13_4864.2]

/-- Complete interval computation for depth 13, residue 4865. -/
theorem bounds_13_4865 : exactInterval 13 4865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4865 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4865) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4865 : oddCount 4865 13 = 6 ∧ acceleratedOrbit 13 4865 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4865 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4865) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4865.1, data_13_4865.2]

/-- Complete interval computation for depth 13, residue 4866. -/
theorem bounds_13_4866 : exactInterval 13 4866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4866 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4866) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4866 : oddCount 4866 13 = 6 ∧ acceleratedOrbit 13 4866 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4866 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4866) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4866.1, data_13_4866.2]

/-- Complete interval computation for depth 13, residue 4867. -/
theorem bounds_13_4867 : exactInterval 13 4867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4867 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4867) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4867 : oddCount 4867 13 = 6 ∧ acceleratedOrbit 13 4867 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4867 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4867) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4867.1, data_13_4867.2]

/-- Complete interval computation for depth 13, residue 4868. -/
theorem bounds_13_4868 : exactInterval 13 4868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4868 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4868) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4868 : oddCount 4868 13 = 5 ∧ acceleratedOrbit 13 4868 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4868 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4868) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4868.1, data_13_4868.2]

/-- Complete interval computation for depth 13, residue 4869. -/
theorem bounds_13_4869 : exactInterval 13 4869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4869 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4869) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4869 : oddCount 4869 13 = 5 ∧ acceleratedOrbit 13 4869 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4869 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4869) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4869.1, data_13_4869.2]

/-- Complete interval computation for depth 13, residue 4870. -/
theorem bounds_13_4870 : exactInterval 13 4870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4870 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4870) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4870 : oddCount 4870 13 = 5 ∧ acceleratedOrbit 13 4870 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4870 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4870) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4870.1, data_13_4870.2]

/-- Complete interval computation for depth 13, residue 4871. -/
theorem bounds_13_4871 : exactInterval 13 4871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4871 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4871) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4871 : oddCount 4871 13 = 7 ∧ acceleratedOrbit 13 4871 = 1301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4871 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4871) = 3 ^ 7 * m + 1301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4871.1, data_13_4871.2]

/-- Complete interval computation for depth 13, residue 4872. -/
theorem bounds_13_4872 : exactInterval 13 4872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4872 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4872) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4872 : oddCount 4872 13 = 5 ∧ acceleratedOrbit 13 4872 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4872 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4872) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4872.1, data_13_4872.2]

/-- Complete interval computation for depth 13, residue 4873. -/
theorem bounds_13_4873 : exactInterval 13 4873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4873 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4873) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4873 : oddCount 4873 13 = 8 ∧ acceleratedOrbit 13 4873 = 3905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4873 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4873) = 3 ^ 8 * m + 3905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4873.1, data_13_4873.2]

end Collatz.Research.StoppingAtlas.Batch0784
