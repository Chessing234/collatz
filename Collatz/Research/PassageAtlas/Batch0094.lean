import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0094

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3047. -/
theorem bounds_15_3047 : exactInterval 15 3047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3047 : oddCount 3047 15 = 8 ∧ acceleratedOrbit 15 3047 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3047) = 3 ^ 8 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3047.1, data_15_3047.2]

/-- Complete interval computation for depth 15, residue 3048. -/
theorem bounds_15_3048 : exactInterval 15 3048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3048 : oddCount 3048 15 = 7 ∧ acceleratedOrbit 15 3048 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3048) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3048.1, data_15_3048.2]

/-- Complete interval computation for depth 15, residue 3049. -/
theorem bounds_15_3049 : exactInterval 15 3049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3049 : oddCount 3049 15 = 12 ∧ acceleratedOrbit 15 3049 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3049) = 3 ^ 12 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3049.1, data_15_3049.2]

/-- Complete interval computation for depth 15, residue 3050. -/
theorem bounds_15_3050 : exactInterval 15 3050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3050 : oddCount 3050 15 = 7 ∧ acceleratedOrbit 15 3050 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3050) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3050.1, data_15_3050.2]

/-- Complete interval computation for depth 15, residue 3051. -/
theorem bounds_15_3051 : exactInterval 15 3051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3051 : oddCount 3051 15 = 9 ∧ acceleratedOrbit 15 3051 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3051) = 3 ^ 9 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3051.1, data_15_3051.2]

/-- Complete interval computation for depth 15, residue 3052. -/
theorem bounds_15_3052 : exactInterval 15 3052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3052 : oddCount 3052 15 = 9 ∧ acceleratedOrbit 15 3052 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3052) = 3 ^ 9 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3052.1, data_15_3052.2]

/-- Complete interval computation for depth 15, residue 3053. -/
theorem bounds_15_3053 : exactInterval 15 3053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3053 : oddCount 3053 15 = 9 ∧ acceleratedOrbit 15 3053 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3053) = 3 ^ 9 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3053.1, data_15_3053.2]

/-- Complete interval computation for depth 15, residue 3054. -/
theorem bounds_15_3054 : exactInterval 15 3054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3054 : oddCount 3054 15 = 9 ∧ acceleratedOrbit 15 3054 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3054) = 3 ^ 9 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3054.1, data_15_3054.2]

/-- Complete interval computation for depth 15, residue 3055. -/
theorem bounds_15_3055 : exactInterval 15 3055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3055 : oddCount 3055 15 = 12 ∧ acceleratedOrbit 15 3055 = 49571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3055) = 3 ^ 12 * m + 49571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3055.1, data_15_3055.2]

/-- Complete interval computation for depth 15, residue 3056. -/
theorem bounds_15_3056 : exactInterval 15 3056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3056 : oddCount 3056 15 = 7 ∧ acceleratedOrbit 15 3056 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3056) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3056.1, data_15_3056.2]

/-- Complete interval computation for depth 15, residue 3057. -/
theorem bounds_15_3057 : exactInterval 15 3057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3057 : oddCount 3057 15 = 7 ∧ acceleratedOrbit 15 3057 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3057) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3057.1, data_15_3057.2]

/-- Complete interval computation for depth 15, residue 3058. -/
theorem bounds_15_3058 : exactInterval 15 3058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3058 : oddCount 3058 15 = 8 ∧ acceleratedOrbit 15 3058 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3058) = 3 ^ 8 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3058.1, data_15_3058.2]

/-- Complete interval computation for depth 15, residue 3059. -/
theorem bounds_15_3059 : exactInterval 15 3059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3059 : oddCount 3059 15 = 8 ∧ acceleratedOrbit 15 3059 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3059) = 3 ^ 8 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3059.1, data_15_3059.2]

/-- Complete interval computation for depth 15, residue 3060. -/
theorem bounds_15_3060 : exactInterval 15 3060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3060 : oddCount 3060 15 = 7 ∧ acceleratedOrbit 15 3060 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3060) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3060.1, data_15_3060.2]

/-- Complete interval computation for depth 15, residue 3061. -/
theorem bounds_15_3061 : exactInterval 15 3061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3061 : oddCount 3061 15 = 7 ∧ acceleratedOrbit 15 3061 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3061) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3061.1, data_15_3061.2]

/-- Complete interval computation for depth 15, residue 3062. -/
theorem bounds_15_3062 : exactInterval 15 3062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3062 : oddCount 3062 15 = 8 ∧ acceleratedOrbit 15 3062 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3062) = 3 ^ 8 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3062.1, data_15_3062.2]

/-- Complete interval computation for depth 15, residue 3063. -/
theorem bounds_15_3063 : exactInterval 15 3063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3063 : oddCount 3063 15 = 8 ∧ acceleratedOrbit 15 3063 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3063) = 3 ^ 8 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3063.1, data_15_3063.2]

/-- Complete interval computation for depth 15, residue 3064. -/
theorem bounds_15_3064 : exactInterval 15 3064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3064 : oddCount 3064 15 = 7 ∧ acceleratedOrbit 15 3064 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3064) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3064.1, data_15_3064.2]

/-- Complete interval computation for depth 15, residue 3065. -/
theorem bounds_15_3065 : exactInterval 15 3065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3065 : oddCount 3065 15 = 10 ∧ acceleratedOrbit 15 3065 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3065) = 3 ^ 10 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3065.1, data_15_3065.2]

/-- Complete interval computation for depth 15, residue 3066. -/
theorem bounds_15_3066 : exactInterval 15 3066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3066 : oddCount 3066 15 = 7 ∧ acceleratedOrbit 15 3066 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3066) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3066.1, data_15_3066.2]

/-- Complete interval computation for depth 15, residue 3067. -/
theorem bounds_15_3067 : exactInterval 15 3067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3067 : oddCount 3067 15 = 9 ∧ acceleratedOrbit 15 3067 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3067) = 3 ^ 9 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3067.1, data_15_3067.2]

/-- Complete interval computation for depth 15, residue 3068. -/
theorem bounds_15_3068 : exactInterval 15 3068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3068 : oddCount 3068 15 = 10 ∧ acceleratedOrbit 15 3068 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3068) = 3 ^ 10 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3068.1, data_15_3068.2]

/-- Complete interval computation for depth 15, residue 3069. -/
theorem bounds_15_3069 : exactInterval 15 3069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3069 : oddCount 3069 15 = 10 ∧ acceleratedOrbit 15 3069 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3069) = 3 ^ 10 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3069.1, data_15_3069.2]

/-- Complete interval computation for depth 15, residue 3070. -/
theorem bounds_15_3070 : exactInterval 15 3070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3070 : oddCount 3070 15 = 10 ∧ acceleratedOrbit 15 3070 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3070) = 3 ^ 10 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3070.1, data_15_3070.2]

/-- Complete interval computation for depth 15, residue 3071. -/
theorem bounds_15_3071 : exactInterval 15 3071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3071 : oddCount 3071 15 = 12 ∧ acceleratedOrbit 15 3071 = 49823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3071) = 3 ^ 12 * m + 49823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3071.1, data_15_3071.2]

/-- Complete interval computation for depth 15, residue 3072. -/
theorem bounds_15_3072 : exactInterval 15 3072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3072 : oddCount 3072 15 = 2 ∧ acceleratedOrbit 15 3072 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3072) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3072.1, data_15_3072.2]

/-- Complete interval computation for depth 15, residue 3073. -/
theorem bounds_15_3073 : exactInterval 15 3073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3073 : oddCount 3073 15 = 7 ∧ acceleratedOrbit 15 3073 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3073) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3073.1, data_15_3073.2]

/-- Complete interval computation for depth 15, residue 3074. -/
theorem bounds_15_3074 : exactInterval 15 3074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3074 : oddCount 3074 15 = 9 ∧ acceleratedOrbit 15 3074 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3074) = 3 ^ 9 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3074.1, data_15_3074.2]

/-- Complete interval computation for depth 15, residue 3075. -/
theorem bounds_15_3075 : exactInterval 15 3075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3075 : oddCount 3075 15 = 9 ∧ acceleratedOrbit 15 3075 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3075) = 3 ^ 9 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3075.1, data_15_3075.2]

/-- Complete interval computation for depth 15, residue 3076. -/
theorem bounds_15_3076 : exactInterval 15 3076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3076 : oddCount 3076 15 = 5 ∧ acceleratedOrbit 15 3076 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3076) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3076.1, data_15_3076.2]

/-- Complete interval computation for depth 15, residue 3077. -/
theorem bounds_15_3077 : exactInterval 15 3077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3077 : oddCount 3077 15 = 5 ∧ acceleratedOrbit 15 3077 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3077) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3077.1, data_15_3077.2]

/-- Complete interval computation for depth 15, residue 3078. -/
theorem bounds_15_3078 : exactInterval 15 3078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3078 : oddCount 3078 15 = 5 ∧ acceleratedOrbit 15 3078 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3078) = 3 ^ 5 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3078.1, data_15_3078.2]

/-- Complete interval computation for depth 15, residue 3079. -/
theorem bounds_15_3079 : exactInterval 15 3079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3079 : oddCount 3079 15 = 9 ∧ acceleratedOrbit 15 3079 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3079) = 3 ^ 9 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3079.1, data_15_3079.2]

end Collatz.Research.PassageAtlas.Batch0094
