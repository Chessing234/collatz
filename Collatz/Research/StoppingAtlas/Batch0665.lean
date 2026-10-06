import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0665

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3031. -/
theorem bounds_13_3031 : exactInterval 13 3031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3031 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3031) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3031 : oddCount 3031 13 = 10 ∧ acceleratedOrbit 13 3031 = 21869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3031 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3031) = 3 ^ 10 * m + 21869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3031.1, data_13_3031.2]

/-- Complete interval computation for depth 13, residue 3032. -/
theorem bounds_13_3032 : exactInterval 13 3032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3032 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3032) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3032 : oddCount 3032 13 = 6 ∧ acceleratedOrbit 13 3032 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3032 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3032) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3032.1, data_13_3032.2]

/-- Complete interval computation for depth 13, residue 3033. -/
theorem bounds_13_3033 : exactInterval 13 3033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3033 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3033) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3033 : oddCount 3033 13 = 3 ∧ acceleratedOrbit 13 3033 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3033 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3033) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3033.1, data_13_3033.2]

/-- Complete interval computation for depth 13, residue 3034. -/
theorem bounds_13_3034 : exactInterval 13 3034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3034 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3034) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3034 : oddCount 3034 13 = 6 ∧ acceleratedOrbit 13 3034 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3034 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3034) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3034.1, data_13_3034.2]

/-- Complete interval computation for depth 13, residue 3035. -/
theorem bounds_13_3035 : exactInterval 13 3035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3035 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3035) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3035 : oddCount 3035 13 = 7 ∧ acceleratedOrbit 13 3035 = 811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3035 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3035) = 3 ^ 7 * m + 811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3035.1, data_13_3035.2]

/-- Complete interval computation for depth 13, residue 3036. -/
theorem bounds_13_3036 : exactInterval 13 3036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3036 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3036) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3036 : oddCount 3036 13 = 6 ∧ acceleratedOrbit 13 3036 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3036 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3036) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3036.1, data_13_3036.2]

/-- Complete interval computation for depth 13, residue 3037. -/
theorem bounds_13_3037 : exactInterval 13 3037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3037 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3037) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3037 : oddCount 3037 13 = 6 ∧ acceleratedOrbit 13 3037 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3037 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3037) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3037.1, data_13_3037.2]

/-- Complete interval computation for depth 13, residue 3038. -/
theorem bounds_13_3038 : exactInterval 13 3038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3038 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3038) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3038 : oddCount 3038 13 = 8 ∧ acceleratedOrbit 13 3038 = 2435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3038 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3038) = 3 ^ 8 * m + 2435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3038.1, data_13_3038.2]

/-- Complete interval computation for depth 13, residue 3039. -/
theorem bounds_13_3039 : exactInterval 13 3039 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3039 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3039) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3039 : oddCount 3039 13 = 8 ∧ acceleratedOrbit 13 3039 = 2435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3039 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3039) = 3 ^ 8 * m + 2435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3039.1, data_13_3039.2]

/-- Complete interval computation for depth 13, residue 3040. -/
theorem bounds_13_3040 : exactInterval 13 3040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3040 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3040) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3040 : oddCount 3040 13 = 5 ∧ acceleratedOrbit 13 3040 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3040 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3040) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3040.1, data_13_3040.2]

/-- Complete interval computation for depth 13, residue 3041. -/
theorem bounds_13_3041 : exactInterval 13 3041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3041 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3041) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3041 : oddCount 3041 13 = 8 ∧ acceleratedOrbit 13 3041 = 2438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3041 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3041) = 3 ^ 8 * m + 2438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3041.1, data_13_3041.2]

/-- Complete interval computation for depth 13, residue 3042. -/
theorem bounds_13_3042 : exactInterval 13 3042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3042 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3042) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3042 : oddCount 3042 13 = 5 ∧ acceleratedOrbit 13 3042 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3042 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3042) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3042.1, data_13_3042.2]

/-- Complete interval computation for depth 13, residue 3043. -/
theorem bounds_13_3043 : exactInterval 13 3043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3043 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3043) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3043 : oddCount 3043 13 = 5 ∧ acceleratedOrbit 13 3043 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3043 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3043) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3043.1, data_13_3043.2]

/-- Complete interval computation for depth 13, residue 3044. -/
theorem bounds_13_3044 : exactInterval 13 3044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3044 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3044) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3044 : oddCount 3044 13 = 6 ∧ acceleratedOrbit 13 3044 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3044 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3044) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3044.1, data_13_3044.2]

/-- Complete interval computation for depth 13, residue 3045. -/
theorem bounds_13_3045 : exactInterval 13 3045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3045 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3045) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3045 : oddCount 3045 13 = 6 ∧ acceleratedOrbit 13 3045 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3045 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3045) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3045.1, data_13_3045.2]

end Collatz.Research.StoppingAtlas.Batch0665
