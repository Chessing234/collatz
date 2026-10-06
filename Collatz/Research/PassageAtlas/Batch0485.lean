import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0485

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15859. -/
theorem bounds_15_15859 : exactInterval 15 15859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15859 : oddCount 15859 15 = 6 ∧ acceleratedOrbit 15 15859 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15859) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15859.1, data_15_15859.2]

/-- Complete interval computation for depth 15, residue 15860. -/
theorem bounds_15_15860 : exactInterval 15 15860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15860 : oddCount 15860 15 = 8 ∧ acceleratedOrbit 15 15860 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15860) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15860.1, data_15_15860.2]

/-- Complete interval computation for depth 15, residue 15861. -/
theorem bounds_15_15861 : exactInterval 15 15861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15861 : oddCount 15861 15 = 8 ∧ acceleratedOrbit 15 15861 = 3179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15861) = 3 ^ 8 * m + 3179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15861.1, data_15_15861.2]

/-- Complete interval computation for depth 15, residue 15862. -/
theorem bounds_15_15862 : exactInterval 15 15862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15862 : oddCount 15862 15 = 10 ∧ acceleratedOrbit 15 15862 = 28592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15862) = 3 ^ 10 * m + 28592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15862.1, data_15_15862.2]

/-- Complete interval computation for depth 15, residue 15863. -/
theorem bounds_15_15863 : exactInterval 15 15863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15863 : oddCount 15863 15 = 10 ∧ acceleratedOrbit 15 15863 = 28592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15863) = 3 ^ 10 * m + 28592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15863.1, data_15_15863.2]

/-- Complete interval computation for depth 15, residue 15864. -/
theorem bounds_15_15864 : exactInterval 15 15864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15864 : oddCount 15864 15 = 8 ∧ acceleratedOrbit 15 15864 = 3178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15864) = 3 ^ 8 * m + 3178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15864.1, data_15_15864.2]

/-- Complete interval computation for depth 15, residue 15865. -/
theorem bounds_15_15865 : exactInterval 15 15865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15865 : oddCount 15865 15 = 6 ∧ acceleratedOrbit 15 15865 = 353 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15865) = 3 ^ 6 * m + 353 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15865.1, data_15_15865.2]

/-- Complete interval computation for depth 15, residue 15866. -/
theorem bounds_15_15866 : exactInterval 15 15866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15866 : oddCount 15866 15 = 8 ∧ acceleratedOrbit 15 15866 = 3178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15866) = 3 ^ 8 * m + 3178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15866.1, data_15_15866.2]

/-- Complete interval computation for depth 15, residue 15867. -/
theorem bounds_15_15867 : exactInterval 15 15867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15867 : oddCount 15867 15 = 9 ∧ acceleratedOrbit 15 15867 = 9533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15867) = 3 ^ 9 * m + 9533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15867.1, data_15_15867.2]

/-- Complete interval computation for depth 15, residue 15868. -/
theorem bounds_15_15868 : exactInterval 15 15868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15868 : oddCount 15868 15 = 8 ∧ acceleratedOrbit 15 15868 = 3178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15868) = 3 ^ 8 * m + 3178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15868.1, data_15_15868.2]

/-- Complete interval computation for depth 15, residue 15869. -/
theorem bounds_15_15869 : exactInterval 15 15869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15869 : oddCount 15869 15 = 8 ∧ acceleratedOrbit 15 15869 = 3178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15869) = 3 ^ 8 * m + 3178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15869.1, data_15_15869.2]

/-- Complete interval computation for depth 15, residue 15870. -/
theorem bounds_15_15870 : exactInterval 15 15870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15870 : oddCount 15870 15 = 13 ∧ acceleratedOrbit 15 15870 = 772253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15870) = 3 ^ 13 * m + 772253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15870.1, data_15_15870.2]

/-- Complete interval computation for depth 15, residue 15871. -/
theorem bounds_15_15871 : exactInterval 15 15871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15871 : oddCount 15871 15 = 13 ∧ acceleratedOrbit 15 15871 = 772253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15871) = 3 ^ 13 * m + 772253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15871.1, data_15_15871.2]

/-- Complete interval computation for depth 15, residue 15872. -/
theorem bounds_15_15872 : exactInterval 15 15872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15872 : oddCount 15872 15 = 5 ∧ acceleratedOrbit 15 15872 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15872) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15872.1, data_15_15872.2]

/-- Complete interval computation for depth 15, residue 15873. -/
theorem bounds_15_15873 : exactInterval 15 15873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15873 : oddCount 15873 15 = 10 ∧ acceleratedOrbit 15 15873 = 28613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15873) = 3 ^ 10 * m + 28613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15873.1, data_15_15873.2]

/-- Complete interval computation for depth 15, residue 15874. -/
theorem bounds_15_15874 : exactInterval 15 15874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15874 : oddCount 15874 15 = 5 ∧ acceleratedOrbit 15 15874 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15874) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15874.1, data_15_15874.2]

/-- Complete interval computation for depth 15, residue 15875. -/
theorem bounds_15_15875 : exactInterval 15 15875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15875 : oddCount 15875 15 = 5 ∧ acceleratedOrbit 15 15875 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15875) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15875.1, data_15_15875.2]

/-- Complete interval computation for depth 15, residue 15876. -/
theorem bounds_15_15876 : exactInterval 15 15876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15876 : oddCount 15876 15 = 7 ∧ acceleratedOrbit 15 15876 = 1061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15876) = 3 ^ 7 * m + 1061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15876.1, data_15_15876.2]

/-- Complete interval computation for depth 15, residue 15877. -/
theorem bounds_15_15877 : exactInterval 15 15877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15877 : oddCount 15877 15 = 7 ∧ acceleratedOrbit 15 15877 = 1061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15877) = 3 ^ 7 * m + 1061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15877.1, data_15_15877.2]

/-- Complete interval computation for depth 15, residue 15878. -/
theorem bounds_15_15878 : exactInterval 15 15878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15878 : oddCount 15878 15 = 7 ∧ acceleratedOrbit 15 15878 = 1061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15878) = 3 ^ 7 * m + 1061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15878.1, data_15_15878.2]

/-- Complete interval computation for depth 15, residue 15879. -/
theorem bounds_15_15879 : exactInterval 15 15879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15879 : oddCount 15879 15 = 7 ∧ acceleratedOrbit 15 15879 = 1060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15879) = 3 ^ 7 * m + 1060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15879.1, data_15_15879.2]

/-- Complete interval computation for depth 15, residue 15880. -/
theorem bounds_15_15880 : exactInterval 15 15880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15880 : oddCount 15880 15 = 5 ∧ acceleratedOrbit 15 15880 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15880) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15880.1, data_15_15880.2]

/-- Complete interval computation for depth 15, residue 15881. -/
theorem bounds_15_15881 : exactInterval 15 15881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15881 : oddCount 15881 15 = 8 ∧ acceleratedOrbit 15 15881 = 3181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15881) = 3 ^ 8 * m + 3181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15881.1, data_15_15881.2]

/-- Complete interval computation for depth 15, residue 15882. -/
theorem bounds_15_15882 : exactInterval 15 15882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15882 : oddCount 15882 15 = 5 ∧ acceleratedOrbit 15 15882 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15882) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15882.1, data_15_15882.2]

/-- Complete interval computation for depth 15, residue 15883. -/
theorem bounds_15_15883 : exactInterval 15 15883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15883 : oddCount 15883 15 = 7 ∧ acceleratedOrbit 15 15883 = 1061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15883) = 3 ^ 7 * m + 1061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15883.1, data_15_15883.2]

/-- Complete interval computation for depth 15, residue 15884. -/
theorem bounds_15_15884 : exactInterval 15 15884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15884 : oddCount 15884 15 = 5 ∧ acceleratedOrbit 15 15884 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15884) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15884.1, data_15_15884.2]

/-- Complete interval computation for depth 15, residue 15885. -/
theorem bounds_15_15885 : exactInterval 15 15885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15885 : oddCount 15885 15 = 5 ∧ acceleratedOrbit 15 15885 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15885) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15885.1, data_15_15885.2]

/-- Complete interval computation for depth 15, residue 15886. -/
theorem bounds_15_15886 : exactInterval 15 15886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15886 : oddCount 15886 15 = 7 ∧ acceleratedOrbit 15 15886 = 1061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15886) = 3 ^ 7 * m + 1061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15886.1, data_15_15886.2]

/-- Complete interval computation for depth 15, residue 15887. -/
theorem bounds_15_15887 : exactInterval 15 15887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15887 : oddCount 15887 15 = 7 ∧ acceleratedOrbit 15 15887 = 1061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15887) = 3 ^ 7 * m + 1061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15887.1, data_15_15887.2]

/-- Complete interval computation for depth 15, residue 15888. -/
theorem bounds_15_15888 : exactInterval 15 15888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15888 : oddCount 15888 15 = 7 ∧ acceleratedOrbit 15 15888 = 1063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15888) = 3 ^ 7 * m + 1063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15888.1, data_15_15888.2]

/-- Complete interval computation for depth 15, residue 15889. -/
theorem bounds_15_15889 : exactInterval 15 15889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15889 : oddCount 15889 15 = 5 ∧ acceleratedOrbit 15 15889 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15889) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15889.1, data_15_15889.2]

/-- Complete interval computation for depth 15, residue 15890. -/
theorem bounds_15_15890 : exactInterval 15 15890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15890 : oddCount 15890 15 = 9 ∧ acceleratedOrbit 15 15890 = 9548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15890) = 3 ^ 9 * m + 9548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15890.1, data_15_15890.2]

/-- Complete interval computation for depth 15, residue 15891. -/
theorem bounds_15_15891 : exactInterval 15 15891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15891 : oddCount 15891 15 = 9 ∧ acceleratedOrbit 15 15891 = 9548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15891) = 3 ^ 9 * m + 9548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15891.1, data_15_15891.2]

end Collatz.Research.PassageAtlas.Batch0485
