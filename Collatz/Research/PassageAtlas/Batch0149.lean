import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0149

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4849. -/
theorem bounds_15_4849 : exactInterval 15 4849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4849 : oddCount 4849 15 = 3 ∧ acceleratedOrbit 15 4849 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4849) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4849.1, data_15_4849.2]

/-- Complete interval computation for depth 15, residue 4850. -/
theorem bounds_15_4850 : exactInterval 15 4850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4850 : oddCount 4850 15 = 12 ∧ acceleratedOrbit 15 4850 = 78731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4850) = 3 ^ 12 * m + 78731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4850.1, data_15_4850.2]

/-- Complete interval computation for depth 15, residue 4851. -/
theorem bounds_15_4851 : exactInterval 15 4851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4851 : oddCount 4851 15 = 12 ∧ acceleratedOrbit 15 4851 = 78731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4851) = 3 ^ 12 * m + 78731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4851.1, data_15_4851.2]

/-- Complete interval computation for depth 15, residue 4852. -/
theorem bounds_15_4852 : exactInterval 15 4852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4852 : oddCount 4852 15 = 7 ∧ acceleratedOrbit 15 4852 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4852) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4852.1, data_15_4852.2]

/-- Complete interval computation for depth 15, residue 4853. -/
theorem bounds_15_4853 : exactInterval 15 4853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4853 : oddCount 4853 15 = 7 ∧ acceleratedOrbit 15 4853 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4853) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4853.1, data_15_4853.2]

/-- Complete interval computation for depth 15, residue 4854. -/
theorem bounds_15_4854 : exactInterval 15 4854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4854 : oddCount 4854 15 = 8 ∧ acceleratedOrbit 15 4854 = 973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4854) = 3 ^ 8 * m + 973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4854.1, data_15_4854.2]

/-- Complete interval computation for depth 15, residue 4855. -/
theorem bounds_15_4855 : exactInterval 15 4855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4855 : oddCount 4855 15 = 8 ∧ acceleratedOrbit 15 4855 = 973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4855) = 3 ^ 8 * m + 973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4855.1, data_15_4855.2]

/-- Complete interval computation for depth 15, residue 4856. -/
theorem bounds_15_4856 : exactInterval 15 4856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4856 : oddCount 4856 15 = 7 ∧ acceleratedOrbit 15 4856 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4856) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4856.1, data_15_4856.2]

/-- Complete interval computation for depth 15, residue 4857. -/
theorem bounds_15_4857 : exactInterval 15 4857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4857 : oddCount 4857 15 = 8 ∧ acceleratedOrbit 15 4857 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4857) = 3 ^ 8 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4857.1, data_15_4857.2]

/-- Complete interval computation for depth 15, residue 4858. -/
theorem bounds_15_4858 : exactInterval 15 4858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4858 : oddCount 4858 15 = 7 ∧ acceleratedOrbit 15 4858 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4858) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4858.1, data_15_4858.2]

/-- Complete interval computation for depth 15, residue 4859. -/
theorem bounds_15_4859 : exactInterval 15 4859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4859 : oddCount 4859 15 = 9 ∧ acceleratedOrbit 15 4859 = 2920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4859) = 3 ^ 9 * m + 2920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4859.1, data_15_4859.2]

/-- Complete interval computation for depth 15, residue 4860. -/
theorem bounds_15_4860 : exactInterval 15 4860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4860 : oddCount 4860 15 = 8 ∧ acceleratedOrbit 15 4860 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4860) = 3 ^ 8 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4860.1, data_15_4860.2]

/-- Complete interval computation for depth 15, residue 4861. -/
theorem bounds_15_4861 : exactInterval 15 4861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4861 : oddCount 4861 15 = 8 ∧ acceleratedOrbit 15 4861 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4861) = 3 ^ 8 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4861.1, data_15_4861.2]

/-- Complete interval computation for depth 15, residue 4862. -/
theorem bounds_15_4862 : exactInterval 15 4862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4862 : oddCount 4862 15 = 8 ∧ acceleratedOrbit 15 4862 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4862) = 3 ^ 8 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4862.1, data_15_4862.2]

/-- Complete interval computation for depth 15, residue 4863. -/
theorem bounds_15_4863 : exactInterval 15 4863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4863 : oddCount 4863 15 = 12 ∧ acceleratedOrbit 15 4863 = 78887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4863) = 3 ^ 12 * m + 78887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4863.1, data_15_4863.2]

/-- Complete interval computation for depth 15, residue 4864. -/
theorem bounds_15_4864 : exactInterval 15 4864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4864 : oddCount 4864 15 = 4 ∧ acceleratedOrbit 15 4864 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4864) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4864.1, data_15_4864.2]

/-- Complete interval computation for depth 15, residue 4865. -/
theorem bounds_15_4865 : exactInterval 15 4865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4865 : oddCount 4865 15 = 7 ∧ acceleratedOrbit 15 4865 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4865) = 3 ^ 7 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4865.1, data_15_4865.2]

/-- Complete interval computation for depth 15, residue 4866. -/
theorem bounds_15_4866 : exactInterval 15 4866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4866 : oddCount 4866 15 = 7 ∧ acceleratedOrbit 15 4866 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4866) = 3 ^ 7 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4866.1, data_15_4866.2]

/-- Complete interval computation for depth 15, residue 4867. -/
theorem bounds_15_4867 : exactInterval 15 4867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4867 : oddCount 4867 15 = 7 ∧ acceleratedOrbit 15 4867 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4867) = 3 ^ 7 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4867.1, data_15_4867.2]

/-- Complete interval computation for depth 15, residue 4868. -/
theorem bounds_15_4868 : exactInterval 15 4868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4868 : oddCount 4868 15 = 6 ∧ acceleratedOrbit 15 4868 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4868) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4868.1, data_15_4868.2]

/-- Complete interval computation for depth 15, residue 4869. -/
theorem bounds_15_4869 : exactInterval 15 4869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4869 : oddCount 4869 15 = 6 ∧ acceleratedOrbit 15 4869 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4869) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4869.1, data_15_4869.2]

/-- Complete interval computation for depth 15, residue 4870. -/
theorem bounds_15_4870 : exactInterval 15 4870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4870 : oddCount 4870 15 = 6 ∧ acceleratedOrbit 15 4870 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4870) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4870.1, data_15_4870.2]

/-- Complete interval computation for depth 15, residue 4871. -/
theorem bounds_15_4871 : exactInterval 15 4871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4871 : oddCount 4871 15 = 8 ∧ acceleratedOrbit 15 4871 = 976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4871) = 3 ^ 8 * m + 976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4871.1, data_15_4871.2]

/-- Complete interval computation for depth 15, residue 4872. -/
theorem bounds_15_4872 : exactInterval 15 4872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4872 : oddCount 4872 15 = 6 ∧ acceleratedOrbit 15 4872 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4872) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4872.1, data_15_4872.2]

/-- Complete interval computation for depth 15, residue 4873. -/
theorem bounds_15_4873 : exactInterval 15 4873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4873 : oddCount 4873 15 = 9 ∧ acceleratedOrbit 15 4873 = 2929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4873) = 3 ^ 9 * m + 2929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4873.1, data_15_4873.2]

/-- Complete interval computation for depth 15, residue 4874. -/
theorem bounds_15_4874 : exactInterval 15 4874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4874 : oddCount 4874 15 = 6 ∧ acceleratedOrbit 15 4874 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4874) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4874.1, data_15_4874.2]

/-- Complete interval computation for depth 15, residue 4875. -/
theorem bounds_15_4875 : exactInterval 15 4875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4875 : oddCount 4875 15 = 8 ∧ acceleratedOrbit 15 4875 = 977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4875) = 3 ^ 8 * m + 977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4875.1, data_15_4875.2]

/-- Complete interval computation for depth 15, residue 4876. -/
theorem bounds_15_4876 : exactInterval 15 4876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4876 : oddCount 4876 15 = 6 ∧ acceleratedOrbit 15 4876 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4876) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4876.1, data_15_4876.2]

/-- Complete interval computation for depth 15, residue 4877. -/
theorem bounds_15_4877 : exactInterval 15 4877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4877 : oddCount 4877 15 = 6 ∧ acceleratedOrbit 15 4877 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4877) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4877.1, data_15_4877.2]

/-- Complete interval computation for depth 15, residue 4878. -/
theorem bounds_15_4878 : exactInterval 15 4878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4878 : oddCount 4878 15 = 6 ∧ acceleratedOrbit 15 4878 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4878) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4878.1, data_15_4878.2]

/-- Complete interval computation for depth 15, residue 4879. -/
theorem bounds_15_4879 : exactInterval 15 4879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4879 : oddCount 4879 15 = 6 ∧ acceleratedOrbit 15 4879 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4879) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4879.1, data_15_4879.2]

/-- Complete interval computation for depth 15, residue 4880. -/
theorem bounds_15_4880 : exactInterval 15 4880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4880 : oddCount 4880 15 = 5 ∧ acceleratedOrbit 15 4880 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4880) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4880.1, data_15_4880.2]

/-- Complete interval computation for depth 15, residue 4881. -/
theorem bounds_15_4881 : exactInterval 15 4881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4881 : oddCount 4881 15 = 6 ∧ acceleratedOrbit 15 4881 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4881) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4881.1, data_15_4881.2]

end Collatz.Research.PassageAtlas.Batch0149
