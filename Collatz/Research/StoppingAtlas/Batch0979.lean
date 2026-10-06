import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0979

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7854. -/
theorem bounds_13_7854 : exactInterval 13 7854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7854 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7854) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7854 : oddCount 7854 13 = 7 ∧ acceleratedOrbit 13 7854 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7854 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7854) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7854.1, data_13_7854.2]

/-- Complete interval computation for depth 13, residue 7855. -/
theorem bounds_13_7855 : exactInterval 13 7855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7855 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7855) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7855 : oddCount 7855 13 = 8 ∧ acceleratedOrbit 13 7855 = 6293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7855 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7855) = 3 ^ 8 * m + 6293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7855.1, data_13_7855.2]

/-- Complete interval computation for depth 13, residue 7856. -/
theorem bounds_13_7856 : exactInterval 13 7856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7856 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7856) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7856 : oddCount 7856 13 = 7 ∧ acceleratedOrbit 13 7856 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7856 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7856) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7856.1, data_13_7856.2]

/-- Complete interval computation for depth 13, residue 7857. -/
theorem bounds_13_7857 : exactInterval 13 7857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7857 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7857) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7857 : oddCount 7857 13 = 6 ∧ acceleratedOrbit 13 7857 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7857 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7857) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7857.1, data_13_7857.2]

/-- Complete interval computation for depth 13, residue 7858. -/
theorem bounds_13_7858 : exactInterval 13 7858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7858 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7858) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7858 : oddCount 7858 13 = 6 ∧ acceleratedOrbit 13 7858 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7858 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7858) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7858.1, data_13_7858.2]

/-- Complete interval computation for depth 13, residue 7859. -/
theorem bounds_13_7859 : exactInterval 13 7859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7859 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7859) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7859 : oddCount 7859 13 = 6 ∧ acceleratedOrbit 13 7859 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7859 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7859) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7859.1, data_13_7859.2]

/-- Complete interval computation for depth 13, residue 7860. -/
theorem bounds_13_7860 : exactInterval 13 7860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7860 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7860) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7860 : oddCount 7860 13 = 7 ∧ acceleratedOrbit 13 7860 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7860 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7860) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7860.1, data_13_7860.2]

/-- Complete interval computation for depth 13, residue 7861. -/
theorem bounds_13_7861 : exactInterval 13 7861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7861 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7861) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7861 : oddCount 7861 13 = 7 ∧ acceleratedOrbit 13 7861 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7861 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7861) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7861.1, data_13_7861.2]

/-- Complete interval computation for depth 13, residue 7862. -/
theorem bounds_13_7862 : exactInterval 13 7862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7862 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7862) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7862 : oddCount 7862 13 = 9 ∧ acceleratedOrbit 13 7862 = 18899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7862 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7862) = 3 ^ 9 * m + 18899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7862.1, data_13_7862.2]

/-- Complete interval computation for depth 13, residue 7863. -/
theorem bounds_13_7863 : exactInterval 13 7863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7863 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7863) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7863 : oddCount 7863 13 = 9 ∧ acceleratedOrbit 13 7863 = 18899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7863 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7863) = 3 ^ 9 * m + 18899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7863.1, data_13_7863.2]

/-- Complete interval computation for depth 13, residue 7864. -/
theorem bounds_13_7864 : exactInterval 13 7864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7864 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7864) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7864 : oddCount 7864 13 = 7 ∧ acceleratedOrbit 13 7864 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7864 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7864) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7864.1, data_13_7864.2]

/-- Complete interval computation for depth 13, residue 7865. -/
theorem bounds_13_7865 : exactInterval 13 7865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7865 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7865) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7865 : oddCount 7865 13 = 7 ∧ acceleratedOrbit 13 7865 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7865 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7865) = 3 ^ 7 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7865.1, data_13_7865.2]

/-- Complete interval computation for depth 13, residue 7866. -/
theorem bounds_13_7866 : exactInterval 13 7866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7866 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7866) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7866 : oddCount 7866 13 = 7 ∧ acceleratedOrbit 13 7866 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7866 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7866) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7866.1, data_13_7866.2]

/-- Complete interval computation for depth 13, residue 7867. -/
theorem bounds_13_7867 : exactInterval 13 7867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7867 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7867) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7867 : oddCount 7867 13 = 7 ∧ acceleratedOrbit 13 7867 = 2101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7867 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7867) = 3 ^ 7 * m + 2101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7867.1, data_13_7867.2]

/-- Complete interval computation for depth 13, residue 7868. -/
theorem bounds_13_7868 : exactInterval 13 7868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7868 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7868) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7868 : oddCount 7868 13 = 6 ∧ acceleratedOrbit 13 7868 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7868 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7868) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7868.1, data_13_7868.2]

end Collatz.Research.StoppingAtlas.Batch0979
