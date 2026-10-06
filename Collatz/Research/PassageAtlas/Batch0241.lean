import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0241

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7864. -/
theorem bounds_15_7864 : exactInterval 15 7864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7864 : oddCount 7864 15 = 8 ∧ acceleratedOrbit 15 7864 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7864) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7864.1, data_15_7864.2]

/-- Complete interval computation for depth 15, residue 7865. -/
theorem bounds_15_7865 : exactInterval 15 7865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7865 : oddCount 7865 15 = 8 ∧ acceleratedOrbit 15 7865 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7865) = 3 ^ 8 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7865.1, data_15_7865.2]

/-- Complete interval computation for depth 15, residue 7866. -/
theorem bounds_15_7866 : exactInterval 15 7866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7866 : oddCount 7866 15 = 8 ∧ acceleratedOrbit 15 7866 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7866) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7866.1, data_15_7866.2]

/-- Complete interval computation for depth 15, residue 7867. -/
theorem bounds_15_7867 : exactInterval 15 7867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7867 : oddCount 7867 15 = 8 ∧ acceleratedOrbit 15 7867 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7867) = 3 ^ 8 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7867.1, data_15_7867.2]

/-- Complete interval computation for depth 15, residue 7868. -/
theorem bounds_15_7868 : exactInterval 15 7868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7868 : oddCount 7868 15 = 7 ∧ acceleratedOrbit 15 7868 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7868) = 3 ^ 7 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7868.1, data_15_7868.2]

/-- Complete interval computation for depth 15, residue 7869. -/
theorem bounds_15_7869 : exactInterval 15 7869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7869 : oddCount 7869 15 = 7 ∧ acceleratedOrbit 15 7869 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7869) = 3 ^ 7 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7869.1, data_15_7869.2]

/-- Complete interval computation for depth 15, residue 7870. -/
theorem bounds_15_7870 : exactInterval 15 7870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7870 : oddCount 7870 15 = 7 ∧ acceleratedOrbit 15 7870 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7870) = 3 ^ 7 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7870.1, data_15_7870.2]

/-- Complete interval computation for depth 15, residue 7871. -/
theorem bounds_15_7871 : exactInterval 15 7871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7871 : oddCount 7871 15 = 10 ∧ acceleratedOrbit 15 7871 = 14186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7871) = 3 ^ 10 * m + 14186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7871.1, data_15_7871.2]

/-- Complete interval computation for depth 15, residue 7872. -/
theorem bounds_15_7872 : exactInterval 15 7872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7872 : oddCount 7872 15 = 5 ∧ acceleratedOrbit 15 7872 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7872) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7872.1, data_15_7872.2]

/-- Complete interval computation for depth 15, residue 7873. -/
theorem bounds_15_7873 : exactInterval 15 7873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7873 : oddCount 7873 15 = 8 ∧ acceleratedOrbit 15 7873 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7873) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7873.1, data_15_7873.2]

/-- Complete interval computation for depth 15, residue 7874. -/
theorem bounds_15_7874 : exactInterval 15 7874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7874 : oddCount 7874 15 = 10 ∧ acceleratedOrbit 15 7874 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7874) = 3 ^ 10 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7874.1, data_15_7874.2]

/-- Complete interval computation for depth 15, residue 7875. -/
theorem bounds_15_7875 : exactInterval 15 7875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7875 : oddCount 7875 15 = 10 ∧ acceleratedOrbit 15 7875 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7875) = 3 ^ 10 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7875.1, data_15_7875.2]

/-- Complete interval computation for depth 15, residue 7876. -/
theorem bounds_15_7876 : exactInterval 15 7876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7876 : oddCount 7876 15 = 4 ∧ acceleratedOrbit 15 7876 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7876) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7876.1, data_15_7876.2]

/-- Complete interval computation for depth 15, residue 7877. -/
theorem bounds_15_7877 : exactInterval 15 7877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7877 : oddCount 7877 15 = 4 ∧ acceleratedOrbit 15 7877 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7877) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7877.1, data_15_7877.2]

/-- Complete interval computation for depth 15, residue 7878. -/
theorem bounds_15_7878 : exactInterval 15 7878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7878 : oddCount 7878 15 = 4 ∧ acceleratedOrbit 15 7878 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7878) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7878.1, data_15_7878.2]

/-- Complete interval computation for depth 15, residue 7879. -/
theorem bounds_15_7879 : exactInterval 15 7879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7879 : oddCount 7879 15 = 8 ∧ acceleratedOrbit 15 7879 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7879) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7879.1, data_15_7879.2]

/-- Complete interval computation for depth 15, residue 7880. -/
theorem bounds_15_7880 : exactInterval 15 7880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7880 : oddCount 7880 15 = 4 ∧ acceleratedOrbit 15 7880 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7880) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7880.1, data_15_7880.2]

/-- Complete interval computation for depth 15, residue 7881. -/
theorem bounds_15_7881 : exactInterval 15 7881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7881 : oddCount 7881 15 = 9 ∧ acceleratedOrbit 15 7881 = 4738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7881) = 3 ^ 9 * m + 4738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7881.1, data_15_7881.2]

/-- Complete interval computation for depth 15, residue 7882. -/
theorem bounds_15_7882 : exactInterval 15 7882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7882 : oddCount 7882 15 = 4 ∧ acceleratedOrbit 15 7882 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7882) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7882.1, data_15_7882.2]

/-- Complete interval computation for depth 15, residue 7883. -/
theorem bounds_15_7883 : exactInterval 15 7883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7883 : oddCount 7883 15 = 10 ∧ acceleratedOrbit 15 7883 = 14215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7883) = 3 ^ 10 * m + 14215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7883.1, data_15_7883.2]

/-- Complete interval computation for depth 15, residue 7884. -/
theorem bounds_15_7884 : exactInterval 15 7884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7884 : oddCount 7884 15 = 4 ∧ acceleratedOrbit 15 7884 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7884) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7884.1, data_15_7884.2]

/-- Complete interval computation for depth 15, residue 7885. -/
theorem bounds_15_7885 : exactInterval 15 7885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7885 : oddCount 7885 15 = 4 ∧ acceleratedOrbit 15 7885 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7885) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7885.1, data_15_7885.2]

/-- Complete interval computation for depth 15, residue 7886. -/
theorem bounds_15_7886 : exactInterval 15 7886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7886 : oddCount 7886 15 = 12 ∧ acceleratedOrbit 15 7886 = 127939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7886) = 3 ^ 12 * m + 127939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7886.1, data_15_7886.2]

/-- Complete interval computation for depth 15, residue 7887. -/
theorem bounds_15_7887 : exactInterval 15 7887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7887 : oddCount 7887 15 = 12 ∧ acceleratedOrbit 15 7887 = 127939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7887) = 3 ^ 12 * m + 127939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7887.1, data_15_7887.2]

/-- Complete interval computation for depth 15, residue 7888. -/
theorem bounds_15_7888 : exactInterval 15 7888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7888 : oddCount 7888 15 = 5 ∧ acceleratedOrbit 15 7888 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7888) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7888.1, data_15_7888.2]

/-- Complete interval computation for depth 15, residue 7889. -/
theorem bounds_15_7889 : exactInterval 15 7889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7889 : oddCount 7889 15 = 7 ∧ acceleratedOrbit 15 7889 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7889) = 3 ^ 7 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7889.1, data_15_7889.2]

/-- Complete interval computation for depth 15, residue 7890. -/
theorem bounds_15_7890 : exactInterval 15 7890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7890 : oddCount 7890 15 = 7 ∧ acceleratedOrbit 15 7890 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7890) = 3 ^ 7 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7890.1, data_15_7890.2]

/-- Complete interval computation for depth 15, residue 7891. -/
theorem bounds_15_7891 : exactInterval 15 7891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7891 : oddCount 7891 15 = 7 ∧ acceleratedOrbit 15 7891 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7891) = 3 ^ 7 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7891.1, data_15_7891.2]

/-- Complete interval computation for depth 15, residue 7892. -/
theorem bounds_15_7892 : exactInterval 15 7892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7892 : oddCount 7892 15 = 5 ∧ acceleratedOrbit 15 7892 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7892) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7892.1, data_15_7892.2]

/-- Complete interval computation for depth 15, residue 7893. -/
theorem bounds_15_7893 : exactInterval 15 7893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7893 : oddCount 7893 15 = 5 ∧ acceleratedOrbit 15 7893 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7893) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7893.1, data_15_7893.2]

/-- Complete interval computation for depth 15, residue 7894. -/
theorem bounds_15_7894 : exactInterval 15 7894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7894 : oddCount 7894 15 = 8 ∧ acceleratedOrbit 15 7894 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7894) = 3 ^ 8 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7894.1, data_15_7894.2]

/-- Complete interval computation for depth 15, residue 7895. -/
theorem bounds_15_7895 : exactInterval 15 7895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7895 : oddCount 7895 15 = 8 ∧ acceleratedOrbit 15 7895 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7895) = 3 ^ 8 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7895.1, data_15_7895.2]

/-- Complete interval computation for depth 15, residue 7896. -/
theorem bounds_15_7896 : exactInterval 15 7896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7896 : oddCount 7896 15 = 6 ∧ acceleratedOrbit 15 7896 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7896) = 3 ^ 6 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7896.1, data_15_7896.2]

end Collatz.Research.PassageAtlas.Batch0241
