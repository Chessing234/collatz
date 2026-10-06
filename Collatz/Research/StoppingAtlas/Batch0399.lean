import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0399

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3041. -/
theorem bounds_12_3041 : exactInterval 12 3041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3041 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3041) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3041 : oddCount 3041 12 = 7 ∧ acceleratedOrbit 12 3041 = 1625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3041 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3041) = 3 ^ 7 * m + 1625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3041.1, data_12_3041.2]

/-- Complete interval computation for depth 12, residue 3042. -/
theorem bounds_12_3042 : exactInterval 12 3042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3042 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3042) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3042 : oddCount 3042 12 = 5 ∧ acceleratedOrbit 12 3042 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3042 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3042) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3042.1, data_12_3042.2]

/-- Complete interval computation for depth 12, residue 3043. -/
theorem bounds_12_3043 : exactInterval 12 3043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3043 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3043) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3043 : oddCount 3043 12 = 5 ∧ acceleratedOrbit 12 3043 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3043 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3043) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3043.1, data_12_3043.2]

/-- Complete interval computation for depth 12, residue 3044. -/
theorem bounds_12_3044 : exactInterval 12 3044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3044 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3044) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3044 : oddCount 3044 12 = 5 ∧ acceleratedOrbit 12 3044 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3044 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3044) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3044.1, data_12_3044.2]

/-- Complete interval computation for depth 12, residue 3045. -/
theorem bounds_12_3045 : exactInterval 12 3045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3045 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3045) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3045 : oddCount 3045 12 = 5 ∧ acceleratedOrbit 12 3045 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3045 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3045) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3045.1, data_12_3045.2]

/-- Complete interval computation for depth 12, residue 3046. -/
theorem bounds_12_3046 : exactInterval 12 3046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3046 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3046) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3046 : oddCount 3046 12 = 5 ∧ acceleratedOrbit 12 3046 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3046 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3046) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3046.1, data_12_3046.2]

/-- Complete interval computation for depth 12, residue 3047. -/
theorem bounds_12_3047 : exactInterval 12 3047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3047 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3047) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3047 : oddCount 3047 12 = 7 ∧ acceleratedOrbit 12 3047 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3047 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3047) = 3 ^ 7 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3047.1, data_12_3047.2]

/-- Complete interval computation for depth 12, residue 3048. -/
theorem bounds_12_3048 : exactInterval 12 3048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3048 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3048) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3048 : oddCount 3048 12 = 5 ∧ acceleratedOrbit 12 3048 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3048 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3048) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3048.1, data_12_3048.2]

/-- Complete interval computation for depth 12, residue 3049. -/
theorem bounds_12_3049 : exactInterval 12 3049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3049 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3049) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3049 : oddCount 3049 12 = 10 ∧ acceleratedOrbit 12 3049 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3049 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3049) = 3 ^ 10 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3049.1, data_12_3049.2]

/-- Complete interval computation for depth 12, residue 3050. -/
theorem bounds_12_3050 : exactInterval 12 3050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3050 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3050) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3050 : oddCount 3050 12 = 5 ∧ acceleratedOrbit 12 3050 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3050 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3050) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3050.1, data_12_3050.2]

/-- Complete interval computation for depth 12, residue 3051. -/
theorem bounds_12_3051 : exactInterval 12 3051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3051 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3051) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3051 : oddCount 3051 12 = 7 ∧ acceleratedOrbit 12 3051 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3051 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3051) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3051.1, data_12_3051.2]

/-- Complete interval computation for depth 12, residue 3052. -/
theorem bounds_12_3052 : exactInterval 12 3052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3052 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3052) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3052 : oddCount 3052 12 = 7 ∧ acceleratedOrbit 12 3052 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3052 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3052) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3052.1, data_12_3052.2]

/-- Complete interval computation for depth 12, residue 3053. -/
theorem bounds_12_3053 : exactInterval 12 3053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3053 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3053) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3053 : oddCount 3053 12 = 7 ∧ acceleratedOrbit 12 3053 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3053 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3053) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3053.1, data_12_3053.2]

/-- Complete interval computation for depth 12, residue 3054. -/
theorem bounds_12_3054 : exactInterval 12 3054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3054 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3054) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3054 : oddCount 3054 12 = 7 ∧ acceleratedOrbit 12 3054 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3054 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3054) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3054.1, data_12_3054.2]

/-- Complete interval computation for depth 12, residue 3055. -/
theorem bounds_12_3055 : exactInterval 12 3055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3055 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3055) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3055 : oddCount 3055 12 = 9 ∧ acceleratedOrbit 12 3055 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3055 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3055) = 3 ^ 9 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3055.1, data_12_3055.2]

end Collatz.Research.StoppingAtlas.Batch0399
