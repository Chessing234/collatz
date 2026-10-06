import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0125

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4063. -/
theorem bounds_15_4063 : exactInterval 15 4063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4063 : oddCount 4063 15 = 8 ∧ acceleratedOrbit 15 4063 = 814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4063) = 3 ^ 8 * m + 814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4063.1, data_15_4063.2]

/-- Complete interval computation for depth 15, residue 4064. -/
theorem bounds_15_4064 : exactInterval 15 4064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4064 : oddCount 4064 15 = 8 ∧ acceleratedOrbit 15 4064 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4064) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4064.1, data_15_4064.2]

/-- Complete interval computation for depth 15, residue 4065. -/
theorem bounds_15_4065 : exactInterval 15 4065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4065 : oddCount 4065 15 = 11 ∧ acceleratedOrbit 15 4065 = 21991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4065) = 3 ^ 11 * m + 21991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4065.1, data_15_4065.2]

/-- Complete interval computation for depth 15, residue 4066. -/
theorem bounds_15_4066 : exactInterval 15 4066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4066 : oddCount 4066 15 = 6 ∧ acceleratedOrbit 15 4066 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4066) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4066.1, data_15_4066.2]

/-- Complete interval computation for depth 15, residue 4067. -/
theorem bounds_15_4067 : exactInterval 15 4067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4067 : oddCount 4067 15 = 6 ∧ acceleratedOrbit 15 4067 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4067) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4067.1, data_15_4067.2]

/-- Complete interval computation for depth 15, residue 4068. -/
theorem bounds_15_4068 : exactInterval 15 4068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4068 : oddCount 4068 15 = 9 ∧ acceleratedOrbit 15 4068 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4068) = 3 ^ 9 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4068.1, data_15_4068.2]

/-- Complete interval computation for depth 15, residue 4069. -/
theorem bounds_15_4069 : exactInterval 15 4069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4069 : oddCount 4069 15 = 9 ∧ acceleratedOrbit 15 4069 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4069) = 3 ^ 9 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4069.1, data_15_4069.2]

/-- Complete interval computation for depth 15, residue 4070. -/
theorem bounds_15_4070 : exactInterval 15 4070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4070 : oddCount 4070 15 = 9 ∧ acceleratedOrbit 15 4070 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4070) = 3 ^ 9 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4070.1, data_15_4070.2]

/-- Complete interval computation for depth 15, residue 4071. -/
theorem bounds_15_4071 : exactInterval 15 4071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4071 : oddCount 4071 15 = 9 ∧ acceleratedOrbit 15 4071 = 2447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4071) = 3 ^ 9 * m + 2447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4071.1, data_15_4071.2]

/-- Complete interval computation for depth 15, residue 4072. -/
theorem bounds_15_4072 : exactInterval 15 4072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4072 : oddCount 4072 15 = 8 ∧ acceleratedOrbit 15 4072 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4072) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4072.1, data_15_4072.2]

/-- Complete interval computation for depth 15, residue 4073. -/
theorem bounds_15_4073 : exactInterval 15 4073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4073 : oddCount 4073 15 = 11 ∧ acceleratedOrbit 15 4073 = 22031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4073) = 3 ^ 11 * m + 22031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4073.1, data_15_4073.2]

/-- Complete interval computation for depth 15, residue 4074. -/
theorem bounds_15_4074 : exactInterval 15 4074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4074 : oddCount 4074 15 = 8 ∧ acceleratedOrbit 15 4074 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4074) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4074.1, data_15_4074.2]

/-- Complete interval computation for depth 15, residue 4075. -/
theorem bounds_15_4075 : exactInterval 15 4075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4075 : oddCount 4075 15 = 9 ∧ acceleratedOrbit 15 4075 = 2449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4075) = 3 ^ 9 * m + 2449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4075.1, data_15_4075.2]

/-- Complete interval computation for depth 15, residue 4076. -/
theorem bounds_15_4076 : exactInterval 15 4076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4076 : oddCount 4076 15 = 8 ∧ acceleratedOrbit 15 4076 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4076) = 3 ^ 8 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4076.1, data_15_4076.2]

/-- Complete interval computation for depth 15, residue 4077. -/
theorem bounds_15_4077 : exactInterval 15 4077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4077 : oddCount 4077 15 = 8 ∧ acceleratedOrbit 15 4077 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4077) = 3 ^ 8 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4077.1, data_15_4077.2]

/-- Complete interval computation for depth 15, residue 4078. -/
theorem bounds_15_4078 : exactInterval 15 4078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4078 : oddCount 4078 15 = 8 ∧ acceleratedOrbit 15 4078 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4078) = 3 ^ 8 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4078.1, data_15_4078.2]

/-- Complete interval computation for depth 15, residue 4079. -/
theorem bounds_15_4079 : exactInterval 15 4079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4079 : oddCount 4079 15 = 8 ∧ acceleratedOrbit 15 4079 = 817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4079) = 3 ^ 8 * m + 817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4079.1, data_15_4079.2]

/-- Complete interval computation for depth 15, residue 4080. -/
theorem bounds_15_4080 : exactInterval 15 4080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4080 : oddCount 4080 15 = 8 ∧ acceleratedOrbit 15 4080 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4080) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4080.1, data_15_4080.2]

/-- Complete interval computation for depth 15, residue 4081. -/
theorem bounds_15_4081 : exactInterval 15 4081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4081 : oddCount 4081 15 = 8 ∧ acceleratedOrbit 15 4081 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4081) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4081.1, data_15_4081.2]

/-- Complete interval computation for depth 15, residue 4082. -/
theorem bounds_15_4082 : exactInterval 15 4082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4082 : oddCount 4082 15 = 9 ∧ acceleratedOrbit 15 4082 = 2456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4082) = 3 ^ 9 * m + 2456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4082.1, data_15_4082.2]

/-- Complete interval computation for depth 15, residue 4083. -/
theorem bounds_15_4083 : exactInterval 15 4083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4083 : oddCount 4083 15 = 9 ∧ acceleratedOrbit 15 4083 = 2456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4083) = 3 ^ 9 * m + 2456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4083.1, data_15_4083.2]

/-- Complete interval computation for depth 15, residue 4084. -/
theorem bounds_15_4084 : exactInterval 15 4084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4084 : oddCount 4084 15 = 8 ∧ acceleratedOrbit 15 4084 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4084) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4084.1, data_15_4084.2]

/-- Complete interval computation for depth 15, residue 4085. -/
theorem bounds_15_4085 : exactInterval 15 4085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4085 : oddCount 4085 15 = 8 ∧ acceleratedOrbit 15 4085 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4085) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4085.1, data_15_4085.2]

/-- Complete interval computation for depth 15, residue 4086. -/
theorem bounds_15_4086 : exactInterval 15 4086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4086 : oddCount 4086 15 = 11 ∧ acceleratedOrbit 15 4086 = 22112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4086) = 3 ^ 11 * m + 22112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4086.1, data_15_4086.2]

/-- Complete interval computation for depth 15, residue 4087. -/
theorem bounds_15_4087 : exactInterval 15 4087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4087 : oddCount 4087 15 = 11 ∧ acceleratedOrbit 15 4087 = 22112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4087) = 3 ^ 11 * m + 22112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4087.1, data_15_4087.2]

/-- Complete interval computation for depth 15, residue 4088. -/
theorem bounds_15_4088 : exactInterval 15 4088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4088 : oddCount 4088 15 = 10 ∧ acceleratedOrbit 15 4088 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4088) = 3 ^ 10 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4088.1, data_15_4088.2]

/-- Complete interval computation for depth 15, residue 4089. -/
theorem bounds_15_4089 : exactInterval 15 4089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4089 : oddCount 4089 15 = 9 ∧ acceleratedOrbit 15 4089 = 2458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4089) = 3 ^ 9 * m + 2458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4089.1, data_15_4089.2]

/-- Complete interval computation for depth 15, residue 4090. -/
theorem bounds_15_4090 : exactInterval 15 4090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4090 : oddCount 4090 15 = 10 ∧ acceleratedOrbit 15 4090 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4090) = 3 ^ 10 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4090.1, data_15_4090.2]

/-- Complete interval computation for depth 15, residue 4091. -/
theorem bounds_15_4091 : exactInterval 15 4091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4091 : oddCount 4091 15 = 9 ∧ acceleratedOrbit 15 4091 = 2459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4091) = 3 ^ 9 * m + 2459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4091.1, data_15_4091.2]

/-- Complete interval computation for depth 15, residue 4092. -/
theorem bounds_15_4092 : exactInterval 15 4092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4092 : oddCount 4092 15 = 10 ∧ acceleratedOrbit 15 4092 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4092) = 3 ^ 10 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4092.1, data_15_4092.2]

/-- Complete interval computation for depth 15, residue 4093. -/
theorem bounds_15_4093 : exactInterval 15 4093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4093 : oddCount 4093 15 = 10 ∧ acceleratedOrbit 15 4093 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4093) = 3 ^ 10 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4093.1, data_15_4093.2]

/-- Complete interval computation for depth 15, residue 4094. -/
theorem bounds_15_4094 : exactInterval 15 4094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4094 : oddCount 4094 15 = 12 ∧ acceleratedOrbit 15 4094 = 66430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4094) = 3 ^ 12 * m + 66430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4094.1, data_15_4094.2]

/-- Complete interval computation for depth 15, residue 4095. -/
theorem bounds_15_4095 : exactInterval 15 4095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4095 : oddCount 4095 15 = 12 ∧ acceleratedOrbit 15 4095 = 66430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4095) = 3 ^ 12 * m + 66430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4095.1, data_15_4095.2]

end Collatz.Research.PassageAtlas.Batch0125
