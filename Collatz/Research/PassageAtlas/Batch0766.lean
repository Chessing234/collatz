import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0766

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25067. -/
theorem bounds_15_25067 : exactInterval 15 25067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25067 : oddCount 25067 15 = 11 ∧ acceleratedOrbit 15 25067 = 135526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25067) = 3 ^ 11 * m + 135526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25067.1, data_15_25067.2]

/-- Complete interval computation for depth 15, residue 25068. -/
theorem bounds_15_25068 : exactInterval 15 25068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25068 : oddCount 25068 15 = 9 ∧ acceleratedOrbit 15 25068 = 15065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25068) = 3 ^ 9 * m + 15065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25068.1, data_15_25068.2]

/-- Complete interval computation for depth 15, residue 25069. -/
theorem bounds_15_25069 : exactInterval 15 25069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25069 : oddCount 25069 15 = 9 ∧ acceleratedOrbit 15 25069 = 15065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25069) = 3 ^ 9 * m + 15065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25069.1, data_15_25069.2]

/-- Complete interval computation for depth 15, residue 25070. -/
theorem bounds_15_25070 : exactInterval 15 25070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25070 : oddCount 25070 15 = 9 ∧ acceleratedOrbit 15 25070 = 15065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25070) = 3 ^ 9 * m + 15065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25070.1, data_15_25070.2]

/-- Complete interval computation for depth 15, residue 25071. -/
theorem bounds_15_25071 : exactInterval 15 25071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25071 : oddCount 25071 15 = 10 ∧ acceleratedOrbit 15 25071 = 45181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25071) = 3 ^ 10 * m + 45181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25071.1, data_15_25071.2]

/-- Complete interval computation for depth 15, residue 25072. -/
theorem bounds_15_25072 : exactInterval 15 25072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25072 : oddCount 25072 15 = 8 ∧ acceleratedOrbit 15 25072 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25072) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25072.1, data_15_25072.2]

/-- Complete interval computation for depth 15, residue 25073. -/
theorem bounds_15_25073 : exactInterval 15 25073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25073 : oddCount 25073 15 = 4 ∧ acceleratedOrbit 15 25073 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25073) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25073.1, data_15_25073.2]

/-- Complete interval computation for depth 15, residue 25074. -/
theorem bounds_15_25074 : exactInterval 15 25074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25074 : oddCount 25074 15 = 10 ∧ acceleratedOrbit 15 25074 = 45197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25074) = 3 ^ 10 * m + 45197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25074.1, data_15_25074.2]

/-- Complete interval computation for depth 15, residue 25075. -/
theorem bounds_15_25075 : exactInterval 15 25075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25075 : oddCount 25075 15 = 10 ∧ acceleratedOrbit 15 25075 = 45197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25075) = 3 ^ 10 * m + 45197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25075.1, data_15_25075.2]

/-- Complete interval computation for depth 15, residue 25076. -/
theorem bounds_15_25076 : exactInterval 15 25076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25076 : oddCount 25076 15 = 8 ∧ acceleratedOrbit 15 25076 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25076) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25076.1, data_15_25076.2]

/-- Complete interval computation for depth 15, residue 25077. -/
theorem bounds_15_25077 : exactInterval 15 25077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25077 : oddCount 25077 15 = 8 ∧ acceleratedOrbit 15 25077 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25077) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25077.1, data_15_25077.2]

/-- Complete interval computation for depth 15, residue 25078. -/
theorem bounds_15_25078 : exactInterval 15 25078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25078 : oddCount 25078 15 = 12 ∧ acceleratedOrbit 15 25078 = 406781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25078) = 3 ^ 12 * m + 406781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25078.1, data_15_25078.2]

/-- Complete interval computation for depth 15, residue 25079. -/
theorem bounds_15_25079 : exactInterval 15 25079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25079 : oddCount 25079 15 = 12 ∧ acceleratedOrbit 15 25079 = 406781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25079) = 3 ^ 12 * m + 406781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25079.1, data_15_25079.2]

/-- Complete interval computation for depth 15, residue 25080. -/
theorem bounds_15_25080 : exactInterval 15 25080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25080 : oddCount 25080 15 = 8 ∧ acceleratedOrbit 15 25080 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25080) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25080.1, data_15_25080.2]

/-- Complete interval computation for depth 15, residue 25081. -/
theorem bounds_15_25081 : exactInterval 15 25081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25081 : oddCount 25081 15 = 9 ∧ acceleratedOrbit 15 25081 = 15068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25081) = 3 ^ 9 * m + 15068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25081.1, data_15_25081.2]

/-- Complete interval computation for depth 15, residue 25082. -/
theorem bounds_15_25082 : exactInterval 15 25082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25082 : oddCount 25082 15 = 8 ∧ acceleratedOrbit 15 25082 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25082) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25082.1, data_15_25082.2]

/-- Complete interval computation for depth 15, residue 25083. -/
theorem bounds_15_25083 : exactInterval 15 25083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25083 : oddCount 25083 15 = 8 ∧ acceleratedOrbit 15 25083 = 5023 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25083) = 3 ^ 8 * m + 5023 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25083.1, data_15_25083.2]

/-- Complete interval computation for depth 15, residue 25084. -/
theorem bounds_15_25084 : exactInterval 15 25084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25084 : oddCount 25084 15 = 9 ∧ acceleratedOrbit 15 25084 = 15070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25084) = 3 ^ 9 * m + 15070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25084.1, data_15_25084.2]

/-- Complete interval computation for depth 15, residue 25085. -/
theorem bounds_15_25085 : exactInterval 15 25085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25085 : oddCount 25085 15 = 9 ∧ acceleratedOrbit 15 25085 = 15070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25085) = 3 ^ 9 * m + 15070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25085.1, data_15_25085.2]

/-- Complete interval computation for depth 15, residue 25086. -/
theorem bounds_15_25086 : exactInterval 15 25086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25086 : oddCount 25086 15 = 9 ∧ acceleratedOrbit 15 25086 = 15070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25086) = 3 ^ 9 * m + 15070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25086.1, data_15_25086.2]

/-- Complete interval computation for depth 15, residue 25087. -/
theorem bounds_15_25087 : exactInterval 15 25087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25087 : oddCount 25087 15 = 12 ∧ acceleratedOrbit 15 25087 = 406885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25087) = 3 ^ 12 * m + 406885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25087.1, data_15_25087.2]

/-- Complete interval computation for depth 15, residue 25088. -/
theorem bounds_15_25088 : exactInterval 15 25088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25088 : oddCount 25088 15 = 2 ∧ acceleratedOrbit 15 25088 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25088) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25088.1, data_15_25088.2]

/-- Complete interval computation for depth 15, residue 25089. -/
theorem bounds_15_25089 : exactInterval 15 25089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25089 : oddCount 25089 15 = 7 ∧ acceleratedOrbit 15 25089 = 1675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25089) = 3 ^ 7 * m + 1675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25089.1, data_15_25089.2]

/-- Complete interval computation for depth 15, residue 25090. -/
theorem bounds_15_25090 : exactInterval 15 25090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25090 : oddCount 25090 15 = 7 ∧ acceleratedOrbit 15 25090 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25090) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25090.1, data_15_25090.2]

/-- Complete interval computation for depth 15, residue 25091. -/
theorem bounds_15_25091 : exactInterval 15 25091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25091 : oddCount 25091 15 = 7 ∧ acceleratedOrbit 15 25091 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25091) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25091.1, data_15_25091.2]

/-- Complete interval computation for depth 15, residue 25092. -/
theorem bounds_15_25092 : exactInterval 15 25092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25092 : oddCount 25092 15 = 7 ∧ acceleratedOrbit 15 25092 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25092) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25092.1, data_15_25092.2]

/-- Complete interval computation for depth 15, residue 25093. -/
theorem bounds_15_25093 : exactInterval 15 25093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25093 : oddCount 25093 15 = 7 ∧ acceleratedOrbit 15 25093 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25093) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25093.1, data_15_25093.2]

/-- Complete interval computation for depth 15, residue 25094. -/
theorem bounds_15_25094 : exactInterval 15 25094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25094 : oddCount 25094 15 = 7 ∧ acceleratedOrbit 15 25094 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25094) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25094.1, data_15_25094.2]

/-- Complete interval computation for depth 15, residue 25095. -/
theorem bounds_15_25095 : exactInterval 15 25095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25095 : oddCount 25095 15 = 9 ∧ acceleratedOrbit 15 25095 = 15076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25095) = 3 ^ 9 * m + 15076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25095.1, data_15_25095.2]

/-- Complete interval computation for depth 15, residue 25096. -/
theorem bounds_15_25096 : exactInterval 15 25096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25096 : oddCount 25096 15 = 6 ∧ acceleratedOrbit 15 25096 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25096) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25096.1, data_15_25096.2]

/-- Complete interval computation for depth 15, residue 25097. -/
theorem bounds_15_25097 : exactInterval 15 25097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25097 : oddCount 25097 15 = 7 ∧ acceleratedOrbit 15 25097 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25097) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25097.1, data_15_25097.2]

/-- Complete interval computation for depth 15, residue 25098. -/
theorem bounds_15_25098 : exactInterval 15 25098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25098 : oddCount 25098 15 = 6 ∧ acceleratedOrbit 15 25098 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25098) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25098.1, data_15_25098.2]

/-- Complete interval computation for depth 15, residue 25099. -/
theorem bounds_15_25099 : exactInterval 15 25099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25099 : oddCount 25099 15 = 7 ∧ acceleratedOrbit 15 25099 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25099) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25099.1, data_15_25099.2]

end Collatz.Research.PassageAtlas.Batch0766
