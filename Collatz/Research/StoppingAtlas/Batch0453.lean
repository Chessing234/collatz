import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0453

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3870. -/
theorem bounds_12_3870 : exactInterval 12 3870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3870 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3870) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3870 : oddCount 3870 12 = 7 ∧ acceleratedOrbit 12 3870 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3870 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3870) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3870.1, data_12_3870.2]

/-- Complete interval computation for depth 12, residue 3871. -/
theorem bounds_12_3871 : exactInterval 12 3871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3871 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3871) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3871 : oddCount 3871 12 = 8 ∧ acceleratedOrbit 12 3871 = 6203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3871 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3871) = 3 ^ 8 * m + 6203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3871.1, data_12_3871.2]

/-- Complete interval computation for depth 12, residue 3872. -/
theorem bounds_12_3872 : exactInterval 12 3872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3872 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3872) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3872 : oddCount 3872 12 = 5 ∧ acceleratedOrbit 12 3872 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3872 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3872) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3872.1, data_12_3872.2]

/-- Complete interval computation for depth 12, residue 3873. -/
theorem bounds_12_3873 : exactInterval 12 3873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3873 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3873) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3873 : oddCount 3873 12 = 5 ∧ acceleratedOrbit 12 3873 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3873 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3873) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3873.1, data_12_3873.2]

/-- Complete interval computation for depth 12, residue 3874. -/
theorem bounds_12_3874 : exactInterval 12 3874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3874 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3874) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3874 : oddCount 3874 12 = 6 ∧ acceleratedOrbit 12 3874 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3874 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3874) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3874.1, data_12_3874.2]

/-- Complete interval computation for depth 12, residue 3875. -/
theorem bounds_12_3875 : exactInterval 12 3875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3875 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3875) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3875 : oddCount 3875 12 = 6 ∧ acceleratedOrbit 12 3875 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3875 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3875) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3875.1, data_12_3875.2]

/-- Complete interval computation for depth 12, residue 3876. -/
theorem bounds_12_3876 : exactInterval 12 3876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3876 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3876) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3876 : oddCount 3876 12 = 6 ∧ acceleratedOrbit 12 3876 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3876 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3876) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3876.1, data_12_3876.2]

/-- Complete interval computation for depth 12, residue 3877. -/
theorem bounds_12_3877 : exactInterval 12 3877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3877 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3877) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3877 : oddCount 3877 12 = 6 ∧ acceleratedOrbit 12 3877 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3877 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3877) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3877.1, data_12_3877.2]

/-- Complete interval computation for depth 12, residue 3878. -/
theorem bounds_12_3878 : exactInterval 12 3878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3878 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3878) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3878 : oddCount 3878 12 = 6 ∧ acceleratedOrbit 12 3878 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3878 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3878) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3878.1, data_12_3878.2]

/-- Complete interval computation for depth 12, residue 3879. -/
theorem bounds_12_3879 : exactInterval 12 3879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3879 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3879) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3879 : oddCount 3879 12 = 7 ∧ acceleratedOrbit 12 3879 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3879 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3879) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3879.1, data_12_3879.2]

/-- Complete interval computation for depth 12, residue 3880. -/
theorem bounds_12_3880 : exactInterval 12 3880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3880 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3880) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3880 : oddCount 3880 12 = 5 ∧ acceleratedOrbit 12 3880 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3880 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3880) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3880.1, data_12_3880.2]

/-- Complete interval computation for depth 12, residue 3881. -/
theorem bounds_12_3881 : exactInterval 12 3881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3881 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3881) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3881 : oddCount 3881 12 = 6 ∧ acceleratedOrbit 12 3881 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3881 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3881) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3881.1, data_12_3881.2]

/-- Complete interval computation for depth 12, residue 3882. -/
theorem bounds_12_3882 : exactInterval 12 3882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3882 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3882) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3882 : oddCount 3882 12 = 5 ∧ acceleratedOrbit 12 3882 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3882 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3882) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3882.1, data_12_3882.2]

/-- Complete interval computation for depth 12, residue 3883. -/
theorem bounds_12_3883 : exactInterval 12 3883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3883 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3883) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3883 : oddCount 3883 12 = 6 ∧ acceleratedOrbit 12 3883 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3883 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3883) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3883.1, data_12_3883.2]

/-- Complete interval computation for depth 12, residue 3884. -/
theorem bounds_12_3884 : exactInterval 12 3884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3884 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3884) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3884 : oddCount 3884 12 = 4 ∧ acceleratedOrbit 12 3884 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3884 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3884) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3884.1, data_12_3884.2]

/-- Complete interval computation for depth 12, residue 3885. -/
theorem bounds_12_3885 : exactInterval 12 3885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3885 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3885) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3885 : oddCount 3885 12 = 4 ∧ acceleratedOrbit 12 3885 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3885 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3885) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3885.1, data_12_3885.2]

end Collatz.Research.StoppingAtlas.Batch0453
