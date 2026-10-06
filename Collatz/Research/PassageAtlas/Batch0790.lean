import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0790

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25853. -/
theorem bounds_15_25853 : exactInterval 15 25853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25853 : oddCount 25853 15 = 10 ∧ acceleratedOrbit 15 25853 = 46595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25853) = 3 ^ 10 * m + 46595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25853.1, data_15_25853.2]

/-- Complete interval computation for depth 15, residue 25854. -/
theorem bounds_15_25854 : exactInterval 15 25854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25854 : oddCount 25854 15 = 11 ∧ acceleratedOrbit 15 25854 = 139781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25854) = 3 ^ 11 * m + 139781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25854.1, data_15_25854.2]

/-- Complete interval computation for depth 15, residue 25855. -/
theorem bounds_15_25855 : exactInterval 15 25855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25855 : oddCount 25855 15 = 11 ∧ acceleratedOrbit 15 25855 = 139781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25855) = 3 ^ 11 * m + 139781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25855.1, data_15_25855.2]

/-- Complete interval computation for depth 15, residue 25856. -/
theorem bounds_15_25856 : exactInterval 15 25856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25856 : oddCount 25856 15 = 3 ∧ acceleratedOrbit 15 25856 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25856) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25856.1, data_15_25856.2]

/-- Complete interval computation for depth 15, residue 25857. -/
theorem bounds_15_25857 : exactInterval 15 25857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25857 : oddCount 25857 15 = 8 ∧ acceleratedOrbit 15 25857 = 5179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25857) = 3 ^ 8 * m + 5179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25857.1, data_15_25857.2]

/-- Complete interval computation for depth 15, residue 25858. -/
theorem bounds_15_25858 : exactInterval 15 25858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25858 : oddCount 25858 15 = 8 ∧ acceleratedOrbit 15 25858 = 5179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25858) = 3 ^ 8 * m + 5179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25858.1, data_15_25858.2]

/-- Complete interval computation for depth 15, residue 25859. -/
theorem bounds_15_25859 : exactInterval 15 25859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25859 : oddCount 25859 15 = 8 ∧ acceleratedOrbit 15 25859 = 5179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25859) = 3 ^ 8 * m + 5179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25859.1, data_15_25859.2]

/-- Complete interval computation for depth 15, residue 25860. -/
theorem bounds_15_25860 : exactInterval 15 25860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25860 : oddCount 25860 15 = 4 ∧ acceleratedOrbit 15 25860 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25860) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25860.1, data_15_25860.2]

/-- Complete interval computation for depth 15, residue 25861. -/
theorem bounds_15_25861 : exactInterval 15 25861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25861 : oddCount 25861 15 = 4 ∧ acceleratedOrbit 15 25861 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25861) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25861.1, data_15_25861.2]

/-- Complete interval computation for depth 15, residue 25862. -/
theorem bounds_15_25862 : exactInterval 15 25862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25862 : oddCount 25862 15 = 4 ∧ acceleratedOrbit 15 25862 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25862) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25862.1, data_15_25862.2]

/-- Complete interval computation for depth 15, residue 25863. -/
theorem bounds_15_25863 : exactInterval 15 25863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25863 : oddCount 25863 15 = 11 ∧ acceleratedOrbit 15 25863 = 139832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25863) = 3 ^ 11 * m + 139832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25863.1, data_15_25863.2]

/-- Complete interval computation for depth 15, residue 25864. -/
theorem bounds_15_25864 : exactInterval 15 25864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25864 : oddCount 25864 15 = 9 ∧ acceleratedOrbit 15 25864 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25864) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25864.1, data_15_25864.2]

/-- Complete interval computation for depth 15, residue 25865. -/
theorem bounds_15_25865 : exactInterval 15 25865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25865 : oddCount 25865 15 = 10 ∧ acceleratedOrbit 15 25865 = 46615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25865) = 3 ^ 10 * m + 46615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25865.1, data_15_25865.2]

/-- Complete interval computation for depth 15, residue 25866. -/
theorem bounds_15_25866 : exactInterval 15 25866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25866 : oddCount 25866 15 = 9 ∧ acceleratedOrbit 15 25866 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25866) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25866.1, data_15_25866.2]

/-- Complete interval computation for depth 15, residue 25867. -/
theorem bounds_15_25867 : exactInterval 15 25867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25867 : oddCount 25867 15 = 9 ∧ acceleratedOrbit 15 25867 = 15542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25867) = 3 ^ 9 * m + 15542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25867.1, data_15_25867.2]

/-- Complete interval computation for depth 15, residue 25868. -/
theorem bounds_15_25868 : exactInterval 15 25868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25868 : oddCount 25868 15 = 9 ∧ acceleratedOrbit 15 25868 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25868) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25868.1, data_15_25868.2]

/-- Complete interval computation for depth 15, residue 25869. -/
theorem bounds_15_25869 : exactInterval 15 25869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25869 : oddCount 25869 15 = 9 ∧ acceleratedOrbit 15 25869 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25869) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25869.1, data_15_25869.2]

/-- Complete interval computation for depth 15, residue 25870. -/
theorem bounds_15_25870 : exactInterval 15 25870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25870 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25870) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25870 : oddCount 25870 15 = 8 ∧ acceleratedOrbit 15 25870 = 5183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25870 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25870) = 3 ^ 8 * m + 5183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25870.1, data_15_25870.2]

/-- Complete interval computation for depth 15, residue 25871. -/
theorem bounds_15_25871 : exactInterval 15 25871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25871 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25871) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25871 : oddCount 25871 15 = 8 ∧ acceleratedOrbit 15 25871 = 5183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25871 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25871) = 3 ^ 8 * m + 5183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25871.1, data_15_25871.2]

/-- Complete interval computation for depth 15, residue 25872. -/
theorem bounds_15_25872 : exactInterval 15 25872 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25872 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25872) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25872 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25872 : oddCount 25872 15 = 6 ∧ acceleratedOrbit 15 25872 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25872 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25872) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25872.1, data_15_25872.2]

/-- Complete interval computation for depth 15, residue 25873. -/
theorem bounds_15_25873 : exactInterval 15 25873 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25873 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25873) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25873 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25873 : oddCount 25873 15 = 9 ∧ acceleratedOrbit 15 25873 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25873 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25873) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25873.1, data_15_25873.2]

/-- Complete interval computation for depth 15, residue 25874. -/
theorem bounds_15_25874 : exactInterval 15 25874 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25874 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25874) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25874 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25874 : oddCount 25874 15 = 9 ∧ acceleratedOrbit 15 25874 = 15545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25874 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25874) = 3 ^ 9 * m + 15545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25874.1, data_15_25874.2]

/-- Complete interval computation for depth 15, residue 25875. -/
theorem bounds_15_25875 : exactInterval 15 25875 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25875 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25875) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25875 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25875 : oddCount 25875 15 = 9 ∧ acceleratedOrbit 15 25875 = 15545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25875 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25875) = 3 ^ 9 * m + 15545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25875.1, data_15_25875.2]

/-- Complete interval computation for depth 15, residue 25876. -/
theorem bounds_15_25876 : exactInterval 15 25876 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25876 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25876) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25876 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25876 : oddCount 25876 15 = 6 ∧ acceleratedOrbit 15 25876 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25876 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25876) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25876.1, data_15_25876.2]

/-- Complete interval computation for depth 15, residue 25877. -/
theorem bounds_15_25877 : exactInterval 15 25877 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25877 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25877) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25877 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25877 : oddCount 25877 15 = 6 ∧ acceleratedOrbit 15 25877 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25877 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25877) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25877.1, data_15_25877.2]

/-- Complete interval computation for depth 15, residue 25878. -/
theorem bounds_15_25878 : exactInterval 15 25878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25878 : oddCount 25878 15 = 9 ∧ acceleratedOrbit 15 25878 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25878) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25878.1, data_15_25878.2]

/-- Complete interval computation for depth 15, residue 25879. -/
theorem bounds_15_25879 : exactInterval 15 25879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25879 : oddCount 25879 15 = 9 ∧ acceleratedOrbit 15 25879 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25879) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25879.1, data_15_25879.2]

/-- Complete interval computation for depth 15, residue 25880. -/
theorem bounds_15_25880 : exactInterval 15 25880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25880 : oddCount 25880 15 = 6 ∧ acceleratedOrbit 15 25880 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25880) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25880.1, data_15_25880.2]

/-- Complete interval computation for depth 15, residue 25881. -/
theorem bounds_15_25881 : exactInterval 15 25881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25881 : oddCount 25881 15 = 10 ∧ acceleratedOrbit 15 25881 = 46646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25881) = 3 ^ 10 * m + 46646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25881.1, data_15_25881.2]

/-- Complete interval computation for depth 15, residue 25882. -/
theorem bounds_15_25882 : exactInterval 15 25882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25882 : oddCount 25882 15 = 6 ∧ acceleratedOrbit 15 25882 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25882) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25882.1, data_15_25882.2]

/-- Complete interval computation for depth 15, residue 25883. -/
theorem bounds_15_25883 : exactInterval 15 25883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25883 : oddCount 25883 15 = 11 ∧ acceleratedOrbit 15 25883 = 139934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25883) = 3 ^ 11 * m + 139934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25883.1, data_15_25883.2]

/-- Complete interval computation for depth 15, residue 25884. -/
theorem bounds_15_25884 : exactInterval 15 25884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25884 : oddCount 25884 15 = 11 ∧ acceleratedOrbit 15 25884 = 139967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25884) = 3 ^ 11 * m + 139967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25884.1, data_15_25884.2]

/-- Complete interval computation for depth 15, residue 25885. -/
theorem bounds_15_25885 : exactInterval 15 25885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25885 : oddCount 25885 15 = 11 ∧ acceleratedOrbit 15 25885 = 139967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25885) = 3 ^ 11 * m + 139967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25885.1, data_15_25885.2]

end Collatz.Research.PassageAtlas.Batch0790
