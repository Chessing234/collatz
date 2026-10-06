import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0666

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3046. -/
theorem bounds_13_3046 : exactInterval 13 3046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3046 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3046) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3046 : oddCount 3046 13 = 6 ∧ acceleratedOrbit 13 3046 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3046 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3046) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3046.1, data_13_3046.2]

/-- Complete interval computation for depth 13, residue 3047. -/
theorem bounds_13_3047 : exactInterval 13 3047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3047 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3047) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3047 : oddCount 3047 13 = 7 ∧ acceleratedOrbit 13 3047 = 814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3047 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3047) = 3 ^ 7 * m + 814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3047.1, data_13_3047.2]

/-- Complete interval computation for depth 13, residue 3048. -/
theorem bounds_13_3048 : exactInterval 13 3048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3048 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3048) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3048 : oddCount 3048 13 = 5 ∧ acceleratedOrbit 13 3048 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3048 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3048) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3048.1, data_13_3048.2]

/-- Complete interval computation for depth 13, residue 3049. -/
theorem bounds_13_3049 : exactInterval 13 3049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3049 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3049) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3049 : oddCount 3049 13 = 10 ∧ acceleratedOrbit 13 3049 = 21991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3049 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3049) = 3 ^ 10 * m + 21991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3049.1, data_13_3049.2]

/-- Complete interval computation for depth 13, residue 3050. -/
theorem bounds_13_3050 : exactInterval 13 3050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3050 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3050) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3050 : oddCount 3050 13 = 5 ∧ acceleratedOrbit 13 3050 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3050 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3050) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3050.1, data_13_3050.2]

/-- Complete interval computation for depth 13, residue 3051. -/
theorem bounds_13_3051 : exactInterval 13 3051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3051 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3051) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3051 : oddCount 3051 13 = 7 ∧ acceleratedOrbit 13 3051 = 815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3051 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3051) = 3 ^ 7 * m + 815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3051.1, data_13_3051.2]

/-- Complete interval computation for depth 13, residue 3052. -/
theorem bounds_13_3052 : exactInterval 13 3052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3052 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3052) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3052 : oddCount 3052 13 = 8 ∧ acceleratedOrbit 13 3052 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3052 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3052) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3052.1, data_13_3052.2]

/-- Complete interval computation for depth 13, residue 3053. -/
theorem bounds_13_3053 : exactInterval 13 3053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3053 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3053) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3053 : oddCount 3053 13 = 8 ∧ acceleratedOrbit 13 3053 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3053 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3053) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3053.1, data_13_3053.2]

/-- Complete interval computation for depth 13, residue 3054. -/
theorem bounds_13_3054 : exactInterval 13 3054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3054 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3054) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3054 : oddCount 3054 13 = 8 ∧ acceleratedOrbit 13 3054 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3054 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3054) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3054.1, data_13_3054.2]

/-- Complete interval computation for depth 13, residue 3055. -/
theorem bounds_13_3055 : exactInterval 13 3055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3055 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3055) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3055 : oddCount 3055 13 = 10 ∧ acceleratedOrbit 13 3055 = 22031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3055 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3055) = 3 ^ 10 * m + 22031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3055.1, data_13_3055.2]

/-- Complete interval computation for depth 13, residue 3056. -/
theorem bounds_13_3056 : exactInterval 13 3056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3056 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3056) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3056 : oddCount 3056 13 = 7 ∧ acceleratedOrbit 13 3056 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3056 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3056) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3056.1, data_13_3056.2]

/-- Complete interval computation for depth 13, residue 3057. -/
theorem bounds_13_3057 : exactInterval 13 3057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3057 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3057) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3057 : oddCount 3057 13 = 5 ∧ acceleratedOrbit 13 3057 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3057 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3057) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3057.1, data_13_3057.2]

/-- Complete interval computation for depth 13, residue 3058. -/
theorem bounds_13_3058 : exactInterval 13 3058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3058 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3058) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3058 : oddCount 3058 13 = 7 ∧ acceleratedOrbit 13 3058 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3058 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3058) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3058.1, data_13_3058.2]

/-- Complete interval computation for depth 13, residue 3059. -/
theorem bounds_13_3059 : exactInterval 13 3059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3059 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3059) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3059 : oddCount 3059 13 = 7 ∧ acceleratedOrbit 13 3059 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3059 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3059) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3059.1, data_13_3059.2]

/-- Complete interval computation for depth 13, residue 3060. -/
theorem bounds_13_3060 : exactInterval 13 3060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3060 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3060) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3060 : oddCount 3060 13 = 7 ∧ acceleratedOrbit 13 3060 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3060 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3060) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3060.1, data_13_3060.2]

end Collatz.Research.StoppingAtlas.Batch0666
