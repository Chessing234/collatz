import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0400

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3056. -/
theorem bounds_12_3056 : exactInterval 12 3056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3056 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3056) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3056 : oddCount 3056 12 = 7 ∧ acceleratedOrbit 12 3056 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3056 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3056) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3056.1, data_12_3056.2]

/-- Complete interval computation for depth 12, residue 3057. -/
theorem bounds_12_3057 : exactInterval 12 3057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3057 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3057) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3057 : oddCount 3057 12 = 5 ∧ acceleratedOrbit 12 3057 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3057 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3057) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3057.1, data_12_3057.2]

/-- Complete interval computation for depth 12, residue 3058. -/
theorem bounds_12_3058 : exactInterval 12 3058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3058 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3058) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3058 : oddCount 3058 12 = 6 ∧ acceleratedOrbit 12 3058 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3058 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3058) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3058.1, data_12_3058.2]

/-- Complete interval computation for depth 12, residue 3059. -/
theorem bounds_12_3059 : exactInterval 12 3059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3059 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3059) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3059 : oddCount 3059 12 = 6 ∧ acceleratedOrbit 12 3059 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3059 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3059) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3059.1, data_12_3059.2]

/-- Complete interval computation for depth 12, residue 3060. -/
theorem bounds_12_3060 : exactInterval 12 3060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3060 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3060) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3060 : oddCount 3060 12 = 7 ∧ acceleratedOrbit 12 3060 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3060 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3060) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3060.1, data_12_3060.2]

/-- Complete interval computation for depth 12, residue 3061. -/
theorem bounds_12_3061 : exactInterval 12 3061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3061 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3061) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3061 : oddCount 3061 12 = 7 ∧ acceleratedOrbit 12 3061 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3061 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3061) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3061.1, data_12_3061.2]

/-- Complete interval computation for depth 12, residue 3062. -/
theorem bounds_12_3062 : exactInterval 12 3062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3062 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3062) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3062 : oddCount 3062 12 = 7 ∧ acceleratedOrbit 12 3062 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3062 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3062) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3062.1, data_12_3062.2]

/-- Complete interval computation for depth 12, residue 3063. -/
theorem bounds_12_3063 : exactInterval 12 3063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3063 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3063) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3063 : oddCount 3063 12 = 7 ∧ acceleratedOrbit 12 3063 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3063 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3063) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3063.1, data_12_3063.2]

/-- Complete interval computation for depth 12, residue 3064. -/
theorem bounds_12_3064 : exactInterval 12 3064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3064 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3064) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3064 : oddCount 3064 12 = 7 ∧ acceleratedOrbit 12 3064 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3064 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3064) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3064.1, data_12_3064.2]

/-- Complete interval computation for depth 12, residue 3065. -/
theorem bounds_12_3065 : exactInterval 12 3065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3065 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3065) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3065 : oddCount 3065 12 = 9 ∧ acceleratedOrbit 12 3065 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3065 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3065) = 3 ^ 9 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3065.1, data_12_3065.2]

/-- Complete interval computation for depth 12, residue 3066. -/
theorem bounds_12_3066 : exactInterval 12 3066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3066 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3066) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3066 : oddCount 3066 12 = 7 ∧ acceleratedOrbit 12 3066 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3066 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3066) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3066.1, data_12_3066.2]

/-- Complete interval computation for depth 12, residue 3067. -/
theorem bounds_12_3067 : exactInterval 12 3067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3067 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3067) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3067 : oddCount 3067 12 = 8 ∧ acceleratedOrbit 12 3067 = 4916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3067 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3067) = 3 ^ 8 * m + 4916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3067.1, data_12_3067.2]

/-- Complete interval computation for depth 12, residue 3068. -/
theorem bounds_12_3068 : exactInterval 12 3068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3068 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3068) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3068 : oddCount 3068 12 = 9 ∧ acceleratedOrbit 12 3068 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3068 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3068) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3068.1, data_12_3068.2]

/-- Complete interval computation for depth 12, residue 3069. -/
theorem bounds_12_3069 : exactInterval 12 3069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3069 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3069) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3069 : oddCount 3069 12 = 9 ∧ acceleratedOrbit 12 3069 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3069 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3069) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3069.1, data_12_3069.2]

/-- Complete interval computation for depth 12, residue 3070. -/
theorem bounds_12_3070 : exactInterval 12 3070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3070 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3070) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3070 : oddCount 3070 12 = 9 ∧ acceleratedOrbit 12 3070 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3070 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3070) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3070.1, data_12_3070.2]

/-- Complete interval computation for depth 12, residue 3071. -/
theorem bounds_12_3071 : exactInterval 12 3071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3071 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3071) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3071 : oddCount 3071 12 = 11 ∧ acceleratedOrbit 12 3071 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3071 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3071) = 3 ^ 11 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3071.1, data_12_3071.2]

end Collatz.Research.StoppingAtlas.Batch0400
