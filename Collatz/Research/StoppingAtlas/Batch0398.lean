import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0398

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3025. -/
theorem bounds_12_3025 : exactInterval 12 3025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3025 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3025) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3025 : oddCount 3025 12 = 7 ∧ acceleratedOrbit 12 3025 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3025 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3025) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3025.1, data_12_3025.2]

/-- Complete interval computation for depth 12, residue 3026. -/
theorem bounds_12_3026 : exactInterval 12 3026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3026 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3026) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3026 : oddCount 3026 12 = 8 ∧ acceleratedOrbit 12 3026 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3026 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3026) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3026.1, data_12_3026.2]

/-- Complete interval computation for depth 12, residue 3027. -/
theorem bounds_12_3027 : exactInterval 12 3027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3027 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3027) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3027 : oddCount 3027 12 = 8 ∧ acceleratedOrbit 12 3027 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3027 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3027) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3027.1, data_12_3027.2]

/-- Complete interval computation for depth 12, residue 3028. -/
theorem bounds_12_3028 : exactInterval 12 3028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3028 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3028) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3028 : oddCount 3028 12 = 5 ∧ acceleratedOrbit 12 3028 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3028 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3028) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3028.1, data_12_3028.2]

/-- Complete interval computation for depth 12, residue 3029. -/
theorem bounds_12_3029 : exactInterval 12 3029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3029 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3029) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3029 : oddCount 3029 12 = 5 ∧ acceleratedOrbit 12 3029 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3029 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3029) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3029.1, data_12_3029.2]

/-- Complete interval computation for depth 12, residue 3030. -/
theorem bounds_12_3030 : exactInterval 12 3030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3030 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3030) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3030 : oddCount 3030 12 = 9 ∧ acceleratedOrbit 12 3030 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3030 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3030) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3030.1, data_12_3030.2]

/-- Complete interval computation for depth 12, residue 3031. -/
theorem bounds_12_3031 : exactInterval 12 3031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3031 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3031) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3031 : oddCount 3031 12 = 9 ∧ acceleratedOrbit 12 3031 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3031 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3031) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3031.1, data_12_3031.2]

/-- Complete interval computation for depth 12, residue 3032. -/
theorem bounds_12_3032 : exactInterval 12 3032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3032 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3032) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3032 : oddCount 3032 12 = 6 ∧ acceleratedOrbit 12 3032 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3032 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3032) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3032.1, data_12_3032.2]

/-- Complete interval computation for depth 12, residue 3033. -/
theorem bounds_12_3033 : exactInterval 12 3033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3033 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3033) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3033 : oddCount 3033 12 = 3 ∧ acceleratedOrbit 12 3033 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3033 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3033) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3033.1, data_12_3033.2]

/-- Complete interval computation for depth 12, residue 3034. -/
theorem bounds_12_3034 : exactInterval 12 3034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3034 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3034) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3034 : oddCount 3034 12 = 6 ∧ acceleratedOrbit 12 3034 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3034 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3034) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3034.1, data_12_3034.2]

/-- Complete interval computation for depth 12, residue 3035. -/
theorem bounds_12_3035 : exactInterval 12 3035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3035 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3035) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3035 : oddCount 3035 12 = 7 ∧ acceleratedOrbit 12 3035 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3035 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3035) = 3 ^ 7 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3035.1, data_12_3035.2]

/-- Complete interval computation for depth 12, residue 3036. -/
theorem bounds_12_3036 : exactInterval 12 3036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3036 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3036) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3036 : oddCount 3036 12 = 6 ∧ acceleratedOrbit 12 3036 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3036 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3036) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3036.1, data_12_3036.2]

/-- Complete interval computation for depth 12, residue 3037. -/
theorem bounds_12_3037 : exactInterval 12 3037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3037 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3037) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3037 : oddCount 3037 12 = 6 ∧ acceleratedOrbit 12 3037 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3037 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3037) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3037.1, data_12_3037.2]

/-- Complete interval computation for depth 12, residue 3038. -/
theorem bounds_12_3038 : exactInterval 12 3038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3038 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3038) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3038 : oddCount 3038 12 = 8 ∧ acceleratedOrbit 12 3038 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3038 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3038) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3038.1, data_12_3038.2]

/-- Complete interval computation for depth 12, residue 3039. -/
theorem bounds_12_3039 : exactInterval 12 3039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3039 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3039) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3039 : oddCount 3039 12 = 8 ∧ acceleratedOrbit 12 3039 = 4870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3039 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3039) = 3 ^ 8 * m + 4870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3039.1, data_12_3039.2]

/-- Complete interval computation for depth 12, residue 3040. -/
theorem bounds_12_3040 : exactInterval 12 3040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3040 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3040) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3040 : oddCount 3040 12 = 5 ∧ acceleratedOrbit 12 3040 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3040 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3040) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3040.1, data_12_3040.2]

end Collatz.Research.StoppingAtlas.Batch0398
