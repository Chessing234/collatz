import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0667

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3061. -/
theorem bounds_13_3061 : exactInterval 13 3061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3061 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3061) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3061 : oddCount 3061 13 = 7 ∧ acceleratedOrbit 13 3061 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3061 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3061) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3061.1, data_13_3061.2]

/-- Complete interval computation for depth 13, residue 3062. -/
theorem bounds_13_3062 : exactInterval 13 3062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3062 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3062) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3062 : oddCount 3062 13 = 8 ∧ acceleratedOrbit 13 3062 = 2456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3062 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3062) = 3 ^ 8 * m + 2456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3062.1, data_13_3062.2]

/-- Complete interval computation for depth 13, residue 3063. -/
theorem bounds_13_3063 : exactInterval 13 3063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3063 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3063) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3063 : oddCount 3063 13 = 8 ∧ acceleratedOrbit 13 3063 = 2456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3063 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3063) = 3 ^ 8 * m + 2456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3063.1, data_13_3063.2]

/-- Complete interval computation for depth 13, residue 3064. -/
theorem bounds_13_3064 : exactInterval 13 3064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3064 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3064) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3064 : oddCount 3064 13 = 7 ∧ acceleratedOrbit 13 3064 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3064 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3064) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3064.1, data_13_3064.2]

/-- Complete interval computation for depth 13, residue 3065. -/
theorem bounds_13_3065 : exactInterval 13 3065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3065 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3065) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3065 : oddCount 3065 13 = 10 ∧ acceleratedOrbit 13 3065 = 22112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3065 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3065) = 3 ^ 10 * m + 22112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3065.1, data_13_3065.2]

/-- Complete interval computation for depth 13, residue 3066. -/
theorem bounds_13_3066 : exactInterval 13 3066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3066 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3066) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3066 : oddCount 3066 13 = 7 ∧ acceleratedOrbit 13 3066 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3066 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3066) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3066.1, data_13_3066.2]

/-- Complete interval computation for depth 13, residue 3067. -/
theorem bounds_13_3067 : exactInterval 13 3067 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3067 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3067) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3067 : oddCount 3067 13 = 8 ∧ acceleratedOrbit 13 3067 = 2458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3067 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3067) = 3 ^ 8 * m + 2458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3067.1, data_13_3067.2]

/-- Complete interval computation for depth 13, residue 3068. -/
theorem bounds_13_3068 : exactInterval 13 3068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3068 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3068) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3068 : oddCount 3068 13 = 9 ∧ acceleratedOrbit 13 3068 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3068 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3068) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3068.1, data_13_3068.2]

/-- Complete interval computation for depth 13, residue 3069. -/
theorem bounds_13_3069 : exactInterval 13 3069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3069 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3069) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3069 : oddCount 3069 13 = 9 ∧ acceleratedOrbit 13 3069 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3069 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3069) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3069.1, data_13_3069.2]

/-- Complete interval computation for depth 13, residue 3070. -/
theorem bounds_13_3070 : exactInterval 13 3070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3070 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3070) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3070 : oddCount 3070 13 = 9 ∧ acceleratedOrbit 13 3070 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3070 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3070) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3070.1, data_13_3070.2]

/-- Complete interval computation for depth 13, residue 3071. -/
theorem bounds_13_3071 : exactInterval 13 3071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3071 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3071) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3071 : oddCount 3071 13 = 11 ∧ acceleratedOrbit 13 3071 = 66430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3071 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3071) = 3 ^ 11 * m + 66430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3071.1, data_13_3071.2]

/-- Complete interval computation for depth 13, residue 3072. -/
theorem bounds_13_3072 : exactInterval 13 3072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3072 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3072) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3072 : oddCount 3072 13 = 2 ∧ acceleratedOrbit 13 3072 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3072 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3072) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3072.1, data_13_3072.2]

/-- Complete interval computation for depth 13, residue 3073. -/
theorem bounds_13_3073 : exactInterval 13 3073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3073 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3073) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3073 : oddCount 3073 13 = 6 ∧ acceleratedOrbit 13 3073 = 274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3073 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3073) = 3 ^ 6 * m + 274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3073.1, data_13_3073.2]

/-- Complete interval computation for depth 13, residue 3074. -/
theorem bounds_13_3074 : exactInterval 13 3074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3074 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3074) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3074 : oddCount 3074 13 = 7 ∧ acceleratedOrbit 13 3074 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3074 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3074) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3074.1, data_13_3074.2]

/-- Complete interval computation for depth 13, residue 3075. -/
theorem bounds_13_3075 : exactInterval 13 3075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3075 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3075) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3075 : oddCount 3075 13 = 7 ∧ acceleratedOrbit 13 3075 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3075 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3075) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3075.1, data_13_3075.2]

/-- Complete interval computation for depth 13, residue 3076. -/
theorem bounds_13_3076 : exactInterval 13 3076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3076 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3076) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3076 : oddCount 3076 13 = 5 ∧ acceleratedOrbit 13 3076 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3076 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3076) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3076.1, data_13_3076.2]

end Collatz.Research.StoppingAtlas.Batch0667
