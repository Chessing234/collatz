import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0387

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2856. -/
theorem bounds_12_2856 : exactInterval 12 2856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2856 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2856) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2856 : oddCount 2856 12 = 3 ∧ acceleratedOrbit 12 2856 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2856 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2856) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2856.1, data_12_2856.2]

/-- Complete interval computation for depth 12, residue 2857. -/
theorem bounds_12_2857 : exactInterval 12 2857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2857 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2857) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2857 : oddCount 2857 12 = 8 ∧ acceleratedOrbit 12 2857 = 4580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2857 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2857) = 3 ^ 8 * m + 4580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2857.1, data_12_2857.2]

/-- Complete interval computation for depth 12, residue 2858. -/
theorem bounds_12_2858 : exactInterval 12 2858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2858 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2858) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2858 : oddCount 2858 12 = 3 ∧ acceleratedOrbit 12 2858 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2858 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2858) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2858.1, data_12_2858.2]

/-- Complete interval computation for depth 12, residue 2859. -/
theorem bounds_12_2859 : exactInterval 12 2859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2859 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2859) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2859 : oddCount 2859 12 = 7 ∧ acceleratedOrbit 12 2859 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2859 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2859) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2859.1, data_12_2859.2]

/-- Complete interval computation for depth 12, residue 2860. -/
theorem bounds_12_2860 : exactInterval 12 2860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2860 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2860) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2860 : oddCount 2860 12 = 6 ∧ acceleratedOrbit 12 2860 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2860 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2860) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2860.1, data_12_2860.2]

/-- Complete interval computation for depth 12, residue 2861. -/
theorem bounds_12_2861 : exactInterval 12 2861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2861 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2861) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2861 : oddCount 2861 12 = 6 ∧ acceleratedOrbit 12 2861 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2861 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2861) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2861.1, data_12_2861.2]

/-- Complete interval computation for depth 12, residue 2862. -/
theorem bounds_12_2862 : exactInterval 12 2862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2862 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2862) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2862 : oddCount 2862 12 = 6 ∧ acceleratedOrbit 12 2862 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2862 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2862) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2862.1, data_12_2862.2]

/-- Complete interval computation for depth 12, residue 2863. -/
theorem bounds_12_2863 : exactInterval 12 2863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2863 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2863) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2863 : oddCount 2863 12 = 8 ∧ acceleratedOrbit 12 2863 = 4589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2863 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2863) = 3 ^ 8 * m + 4589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2863.1, data_12_2863.2]

/-- Complete interval computation for depth 12, residue 2864. -/
theorem bounds_12_2864 : exactInterval 12 2864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2864 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2864) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2864 : oddCount 2864 12 = 3 ∧ acceleratedOrbit 12 2864 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2864 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2864) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2864.1, data_12_2864.2]

/-- Complete interval computation for depth 12, residue 2865. -/
theorem bounds_12_2865 : exactInterval 12 2865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2865 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2865) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2865 : oddCount 2865 12 = 6 ∧ acceleratedOrbit 12 2865 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2865 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2865) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2865.1, data_12_2865.2]

/-- Complete interval computation for depth 12, residue 2866. -/
theorem bounds_12_2866 : exactInterval 12 2866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2866 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2866) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2866 : oddCount 2866 12 = 6 ∧ acceleratedOrbit 12 2866 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2866 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2866) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2866.1, data_12_2866.2]

/-- Complete interval computation for depth 12, residue 2867. -/
theorem bounds_12_2867 : exactInterval 12 2867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2867 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2867) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2867 : oddCount 2867 12 = 6 ∧ acceleratedOrbit 12 2867 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2867 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2867) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2867.1, data_12_2867.2]

/-- Complete interval computation for depth 12, residue 2868. -/
theorem bounds_12_2868 : exactInterval 12 2868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2868 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2868) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2868 : oddCount 2868 12 = 3 ∧ acceleratedOrbit 12 2868 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2868 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2868) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2868.1, data_12_2868.2]

/-- Complete interval computation for depth 12, residue 2869. -/
theorem bounds_12_2869 : exactInterval 12 2869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2869 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2869) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2869 : oddCount 2869 12 = 3 ∧ acceleratedOrbit 12 2869 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2869 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2869) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2869.1, data_12_2869.2]

/-- Complete interval computation for depth 12, residue 2870. -/
theorem bounds_12_2870 : exactInterval 12 2870 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2870 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2870) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2870 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2870 : oddCount 2870 12 = 7 ∧ acceleratedOrbit 12 2870 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2870 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2870) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2870.1, data_12_2870.2]

/-- Complete interval computation for depth 12, residue 2871. -/
theorem bounds_12_2871 : exactInterval 12 2871 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2871 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2871) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2871 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2871 : oddCount 2871 12 = 7 ∧ acceleratedOrbit 12 2871 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2871 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2871) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2871.1, data_12_2871.2]

end Collatz.Research.StoppingAtlas.Batch0387
