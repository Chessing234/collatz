import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0732

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4060. -/
theorem bounds_13_4060 : exactInterval 13 4060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4060 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4060) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4060 : oddCount 4060 13 = 6 ∧ acceleratedOrbit 13 4060 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4060 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4060) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4060.1, data_13_4060.2]

/-- Complete interval computation for depth 13, residue 4061. -/
theorem bounds_13_4061 : exactInterval 13 4061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4061 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4061) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4061 : oddCount 4061 13 = 6 ∧ acceleratedOrbit 13 4061 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4061 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4061) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4061.1, data_13_4061.2]

/-- Complete interval computation for depth 13, residue 4062. -/
theorem bounds_13_4062 : exactInterval 13 4062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4062 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4062) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4062 : oddCount 4062 13 = 7 ∧ acceleratedOrbit 13 4062 = 1085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4062 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4062) = 3 ^ 7 * m + 1085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4062.1, data_13_4062.2]

/-- Complete interval computation for depth 13, residue 4063. -/
theorem bounds_13_4063 : exactInterval 13 4063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4063 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4063) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4063 : oddCount 4063 13 = 7 ∧ acceleratedOrbit 13 4063 = 1085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4063 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4063) = 3 ^ 7 * m + 1085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4063.1, data_13_4063.2]

/-- Complete interval computation for depth 13, residue 4064. -/
theorem bounds_13_4064 : exactInterval 13 4064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4064 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4064) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4064 : oddCount 4064 13 = 7 ∧ acceleratedOrbit 13 4064 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4064 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4064) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4064.1, data_13_4064.2]

/-- Complete interval computation for depth 13, residue 4065. -/
theorem bounds_13_4065 : exactInterval 13 4065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4065 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4065) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4065 : oddCount 4065 13 = 10 ∧ acceleratedOrbit 13 4065 = 29321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4065 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4065) = 3 ^ 10 * m + 29321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4065.1, data_13_4065.2]

/-- Complete interval computation for depth 13, residue 4066. -/
theorem bounds_13_4066 : exactInterval 13 4066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4066 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4066) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4066 : oddCount 4066 13 = 6 ∧ acceleratedOrbit 13 4066 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4066 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4066) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4066.1, data_13_4066.2]

/-- Complete interval computation for depth 13, residue 4067. -/
theorem bounds_13_4067 : exactInterval 13 4067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4067 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4067) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4067 : oddCount 4067 13 = 6 ∧ acceleratedOrbit 13 4067 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4067 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4067) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4067.1, data_13_4067.2]

/-- Complete interval computation for depth 13, residue 4068. -/
theorem bounds_13_4068 : exactInterval 13 4068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4068 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4068) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4068 : oddCount 4068 13 = 8 ∧ acceleratedOrbit 13 4068 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4068 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4068) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4068.1, data_13_4068.2]

/-- Complete interval computation for depth 13, residue 4069. -/
theorem bounds_13_4069 : exactInterval 13 4069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4069 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4069) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4069 : oddCount 4069 13 = 8 ∧ acceleratedOrbit 13 4069 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4069 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4069) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4069.1, data_13_4069.2]

/-- Complete interval computation for depth 13, residue 4070. -/
theorem bounds_13_4070 : exactInterval 13 4070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4070 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4070) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4070 : oddCount 4070 13 = 8 ∧ acceleratedOrbit 13 4070 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4070 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4070) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4070.1, data_13_4070.2]

/-- Complete interval computation for depth 13, residue 4071. -/
theorem bounds_13_4071 : exactInterval 13 4071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4071 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4071) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4071 : oddCount 4071 13 = 8 ∧ acceleratedOrbit 13 4071 = 3262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4071 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4071) = 3 ^ 8 * m + 3262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4071.1, data_13_4071.2]

/-- Complete interval computation for depth 13, residue 4072. -/
theorem bounds_13_4072 : exactInterval 13 4072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4072 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4072) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4072 : oddCount 4072 13 = 7 ∧ acceleratedOrbit 13 4072 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4072 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4072) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4072.1, data_13_4072.2]

/-- Complete interval computation for depth 13, residue 4073. -/
theorem bounds_13_4073 : exactInterval 13 4073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4073 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4073) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4073 : oddCount 4073 13 = 9 ∧ acceleratedOrbit 13 4073 = 9791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4073 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4073) = 3 ^ 9 * m + 9791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4073.1, data_13_4073.2]

/-- Complete interval computation for depth 13, residue 4074. -/
theorem bounds_13_4074 : exactInterval 13 4074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4074 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4074) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4074 : oddCount 4074 13 = 7 ∧ acceleratedOrbit 13 4074 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4074 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4074) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4074.1, data_13_4074.2]

end Collatz.Research.StoppingAtlas.Batch0732
